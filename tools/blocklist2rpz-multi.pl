#!/usr/bin/perl

###############################################################################
# blocklist2rpz-multi.pl - Multi-Source Blocklist to RPZ Converter (Ultimate)
#
# Features:
#   - Supports machine-readable urllist.txt in <category>,<url> format
#   - Automatically categorizes and stores .rpz files in category subdirectories
#   - Warns if a GitHub HTML URL is detected (suggests RAW URL)
#   - Tabular status summary at the end (lists, domains, time per list, total time)
#   - Failed sources are listed in the error log and "Failed sources" section
#   - Optionally writes status report to file (--status-report/-s)
#   - RPZ/domain validation for all generated .rpz files (--validate/-V)
#   - Optionally writes validation report to file (--validation-report)
#   - Wildcard support (--wildcards/-w)
#   - Optional SOA/NS record exclusion (--no-soa/-n)
#   - Flexible logging: logs stored in tools/logs/ and excluded via .gitignore
#   - Reads list-mappings.csv to use custom filenames for RPZ files
#   - Adds license and source comments from list-mappings.csv to RPZ headers
#   - Checks for changes using ETag/Last-Modified or content hash
#   - Stores metadata in tools/logs/source_metadata.json
#   - Generates SOURCES.md with source overview including license
#
# Usage:
#   perl blocklist2rpz-multi.pl [options]
#
# Options:
#   --wildcards, -w             Output wildcard RPZ entries (*.<domain> CNAME .)
#   --output-dir, -d <dir>      Output base directory for RPZ files (default: .)
#   --urllist, -l <file>        File with <category>,<url> per line (CSV format)
#   --list-mappings, -m <file>  File with <url>,<category>,<filename>,<comments>
#   --error-log, -e <file>      Write unreachable or failed sources to this log file
#   --no-soa, -n                Do not output SOA and NS records in the RPZ file
#   --status-report, -s <file>  Write processing summary to this file
#   --validate, -V              Validate all generated RPZ files for syntax and domain errors
#   --validation-report <file>  Write validation report to this file
#   --help, -h                  Show this help message
#
# Example:
#   perl $0 -w -d ./ -l tools/urllist.txt -m tools/list-mappings.csv \
#     -e tools/logs/error_$(date +%Y%m%d_%H%M%S).log \
#     -s tools/logs/status_$(date +%Y%m%d_%H%M%S).txt \
#     --validate --validation-report tools/logs/validation_$(date +%Y%m%d_%H%M%S).txt
#
# Notes:
#   - .rpz files are stored in category subdirectories (e.g., ads/, malware/, etc.)
#   - Logs and metadata are stored in tools/logs/ and excluded via .gitignore
#   - urllist.txt must use the <category>,<url> format
#   - list-mappings.csv must use the <url>,<category>,<filename>,<comments> format
#
# Version: 1.5 (fixed wide character error with UTF-8 encoding)
# Author: ummeegge, with community contributions
###############################################################################

use strict;
use warnings;
use LWP::UserAgent;
use Getopt::Long;
use POSIX qw(strftime);
use File::Basename;
use File::Path qw(make_path);
use URI;
use open ':std', ':encoding(UTF-8)';
use Text::CSV;
use JSON;
use Digest::SHA qw(sha256_hex);
use File::Slurp;
use Encode qw(encode);

# --- Command-line option variables ---
my $wildcards         = 0;
my $output_dir        = '.';
my $help              = 0;
my $urllist           = '';
my $list_mappings     = '';
my $error_log         = '';
my $no_soa            = 0;
my $status_report     = '';
my $validate          = 0;
my $validation_report = '';

GetOptions(
    'wildcards|w'           => \$wildcards,
    'output-dir|d=s'        => \$output_dir,
    'urllist|l=s'           => \$urllist,
    'list-mappings|m=s'     => \$list_mappings,
    'error-log|e=s'         => \$error_log,
    'no-soa|n'              => \$no_soa,
    'status-report|s=s'     => \$status_report,
    'validate|V'            => \$validate,
    'validation-report=s'   => \$validation_report,
    'help|h'                => \$help,
) or die "Error in command line arguments. Use --help for usage.\n";

if ($help or (!$urllist && !@ARGV)) {
    print <<"USAGE";
Usage: $0 [options]
Options:
  --wildcards, -w             Output wildcard RPZ entries (*.<domain> CNAME .)
  --output-dir, -d <dir>      Output directory for RPZ files (default: .)
  --urllist, -l <file>        File with category,url per line (see README)
  --list-mappings, -m <file>  File with url,category,filename,comments to map URLs to custom RPZ filenames
  --error-log, -e <file>      Write unreachable or failed sources to this log file
  --no-soa, -n                Do not output SOA and NS records in the RPZ file
  --status-report, -s <file>  Write processing summary to this file
  --validate, -V              Validate all generated RPZ files for syntax and domain errors
  --validation-report <file>  Write validation report to this file
  --help, -h                  Show this help message
Example:
  perl $0 -w -d ./ -l tools/urllist.txt -m tools/list-mappings.csv --validate --validation-report tools/validation.txt
USAGE
    exit 0;
}

# --- Prepare HTTP user agent for downloads ---
my $ua = LWP::UserAgent->new(timeout => 20);

# --- Open error log file if requested ---
my $err_fh;
if ($error_log) {
    open $err_fh, '>>', $error_log or die "Cannot open error log file '$error_log': $!\n";
    print $err_fh "\n=== Blocklist2RPZ Run at " . localtime() . " ===\n";
}

# --- Status tracking ---
my %list_stats;
my $total_domains = 0;
my $lists_ok      = 0;
my $lists_err     = 0;
my @error_sources;

# --- Time tracking ---
my $global_start = time();

# --- Load source metadata ---
my $metadata_file = "$output_dir/tools/logs/source_metadata.json";
my %source_metadata = -e $metadata_file ? %{ decode_json(read_file($metadata_file)) } : ();

# --- Read list mappings from list-mappings.csv ---
my %url_to_filename;
if ($list_mappings) {
    my $csv = Text::CSV->new({ binary => 1, sep_char => ',', auto_diag => 1 });
    open my $mfh, '<:encoding(utf8)', $list_mappings or die "Can't open list-mappings file '$list_mappings': $!\n";
    $csv->getline($mfh); # Skip header
    while (my $row = $csv->getline($mfh)) {
        next unless @$row >= 3;
        my ($url, $category, $filename, $comments) = @$row;
        $url_to_filename{$url} = { category => $category, filename => $filename, comments => $comments };
    }
    close $mfh;
}

# --- Read categorized sources from urllist.txt ---
my @categorized_sources;
if ($urllist) {
    open my $ufh, '<', $urllist or die "Cannot open urllist file '$urllist': $!\n";
    while (my $line = <$ufh>) {
        chomp $line;
        $line =~ s/^\s+|\s+$//g;
        next if $line =~ /^\s*(#.*)?$/;
        if ($line =~ /^([a-zA-Z0-9_-]+),(https?:\/\/.+)$/) {
            my ($cat, $url) = ($1, $2);
            push @categorized_sources, { category => $cat, url => $url };
        }
    }
    close $ufh;
}

# --- Process each categorized source ---
foreach my $entry (@categorized_sources) {
    my $category = $entry->{category};
    my $source   = $entry->{url};
    my $output_dir_for_cat = "$output_dir/$category";
    unless (-d $output_dir_for_cat) {
        make_path($output_dir_for_cat) or die "Cannot create output directory '$output_dir_for_cat': $!\n";
    }

    my $list_start = time();
    my $content = '';
    my $source_label = $source;

    # --- Check for GitHub HTML URLs ---
    if ($source =~ m{^https://github\.com/([^/]+/[^/]+)/blob/(.+)$}) {
        my $raw_url = "https://raw.githubusercontent.com/$1/$2";
        warn "\n[WARNING] HTML GitHub URL detected: $source\nUse RAW URL: $raw_url\n\n";
        print $err_fh "[WARNING] HTML GitHub URL detected: $source\n" if $err_fh;
        push @error_sources, $source;
        $list_stats{$source_label} = { domains => 0, error => 1, time => 0 };
        $lists_err++;
        next;
    }

    # --- Check for changes using HTTP headers ---
    my $current_metadata = $source_metadata{$source} // { etag => '', last_modified => '', hash => '', domains => 0 };
    my $skip_processing = 0;

    if ($source =~ m{^https?://}) {
        my $req = HTTP::Request->new(HEAD => $source);
        my $resp = $ua->request($req);
        unless ($resp->is_success) {
            my $msg = "HEAD request failed for $source: " . $resp->status_line . "\n";
            warn $msg;
            print $err_fh $msg if $err_fh;
            push @error_sources, $source;
            $list_stats{$source_label} = { domains => 0, error => 1, time => 0 };
            $lists_err++;
            next;
        }

        my $etag = $resp->header('ETag') // '';
        my $last_modified = $resp->header('Last-Modified') // '';

        if ($etag eq $current_metadata->{etag} && $last_modified eq $current_metadata->{last_modified}) {
            print "No changes for $source (ETag/Last-Modified unchanged), skipping.\n";
            $list_stats{$source_label} = { domains => $current_metadata->{domains}, error => 0, time => 0 };
            $lists_ok++;
            $skip_processing = 1;
        } else {
            # Download source
            $resp = $ua->get($source);
            unless ($resp->is_success) {
                my $msg = "Could not fetch $source: " . $resp->status_line . "\n";
                warn $msg;
                print $err_fh $msg if $err_fh;
                push @error_sources, $source;
                $list_stats{$source_label} = { domains => 0, error => 1, time => 0 };
                $lists_err++;
                next;
            }
            $content = $resp->decoded_content;
            my $content_hash = sha256_hex(encode('UTF-8', $content));
            # Fallback: Check content hash
            if ($content_hash eq $current_metadata->{hash}) {
                print "No changes for $source (hash unchanged), skipping.\n";
                $list_stats{$source_label} = { domains => $current_metadata->{domains}, error => 0, time => 0 };
                $lists_ok++;
                $skip_processing = 1;
            } else {
                $source_metadata{$source} = {
                    etag => $etag,
                    last_modified => $last_modified,
                    hash => $content_hash,
                    domains => 0, # Will be updated after processing
                    last_updated => time(),
                };
            }
        }
    } else {
        # Handle local files
        my $fh;
        unless (open($fh, '<', $source)) {
            my $msg = "Cannot open $source: $!\n";
            warn $msg;
            print $err_fh $msg if $err_fh;
            push @error_sources, $source;
            $list_stats{$source_label} = { domains => 0, error => 1, time => 0 };
            $lists_err++;
            next;
        }
        local $/;
        $content = <$fh>;
        close $fh;
        my $content_hash = sha256_hex(encode('UTF-8', $content));
        if ($content_hash eq $current_metadata->{hash}) {
            print "No changes for $source (hash unchanged), skipping.\n";
            $list_stats{$source_label} = { domains => $current_metadata->{domains}, error => 0, time => 0 };
            $lists_ok++;
            $skip_processing = 1;
        } else {
            $source_metadata{$source} = {
                etag => '',
                last_modified => '',
                hash => $content_hash,
                domains => 0, # Will be updated after processing
                last_updated => time(),
            };
        }
        $source_label = basename($source);
    }

    # Skip processing if no changes
    next if $skip_processing;

    # --- Determine output filename and comments ---
    my $outfile;
    my $comments = "No comments provided";
    if (exists $url_to_filename{$source} && $url_to_filename{$source}{filename}) {
        $outfile = "$output_dir_for_cat/$url_to_filename{$source}{filename}";
        $source_label = $url_to_filename{$source}{filename};
        $comments = $url_to_filename{$source}{comments} if $url_to_filename{$source}{comments};
    } else {
        $source_label =~ s/[^a-zA-Z0-9_.-]/_/g;
        $source_label =~ s/\.(txt|csv|tsv|list|php)$//i;
        $outfile = "$output_dir_for_cat/$source_label.rpz";
    }

    my ($rpz_data, $entry_count) = convert_blocklist_to_rpz($content, $source, $wildcards, $no_soa, $comments);

    my $out;
    unless (open($out, '>', $outfile)) {
        my $msg = "Cannot write $outfile: $!\n";
        warn $msg;
        print $err_fh $msg if $err_fh;
        push @error_sources, $source;
        $list_stats{$source_label} = { domains => 0, error => 1, time => 0 };
        $lists_err++;
        next;
    }
    print $out $rpz_data;
    close $out;
    print "Wrote $outfile\n";

    # Update metadata with domain count
    $source_metadata{$source}{domains} = $entry_count;

    my $list_time = time() - $list_start;
    $list_stats{$source_label} = { domains => $entry_count, error => 0, time => $list_time };
    $total_domains += $entry_count;
    $lists_ok++;
}

# --- Save metadata ---
make_path("$output_dir/tools/logs") unless -d "$output_dir/tools/logs";
write_file($metadata_file, encode_json(\%source_metadata));

my $global_time = time() - $global_start;
close $err_fh if $err_fh;

# --- Status report ---
my $status = '';
$status .= "\n========== Blocklist2RPZ Status Report ==========\n";
$status .= "Date: " . scalar(localtime) . "\n";
$status .= "Lists processed: " . scalar(@categorized_sources) . "\n";
$status .= "  Successful: $lists_ok\n";
$status .= "  Failed:     $lists_err\n";
$status .= "Total domains (all lists): $total_domains\n";
$status .= sprintf("Total run time: %.2fs\n", $global_time);
$status .= "\n";
$status .= sprintf("%-35s %12s %12s\n", "List", "Domains", "Time (s)");
$status .= "-" x 62 . "\n";
foreach my $label (sort keys %list_stats) {
    my $stat = $list_stats{$label};
    if ($stat->{error}) {
        $status .= sprintf("%-35s %12s %12s\n", $label, "ERROR", "-");
    } else {
        $status .= sprintf("%-35s %12d %12.2f\n", $label, $stat->{domains}, $stat->{time});
    }
}
if (@error_sources) {
    $status .= "\nFailed sources:\n";
    $status .= join("\n", map { "  $_" } @error_sources) . "\n";
}
$status .= "================================================\n";

print $status;

if ($status_report) {
    open(my $sfh, '>', $status_report) or warn "Cannot write status report file '$status_report': $!\n";
    print $sfh $status;
    close $sfh;
}

# --- Generate SOURCES.md ---
my $sources_md = "# Source Lists Overview\n\n";
$sources_md .= "This file provides an overview of the blocklists used in this project, including their category, last update time, number of entries, and license.\n\n";
$sources_md .= "| Source URL | Category | Last Updated | Entries | License |\n";
$sources_md .= "|------------|----------|--------------|---------|---------|\n";
foreach my $entry (@categorized_sources) {
    my $url = $entry->{url};
    my $category = $entry->{category};
    my $last_updated = $source_metadata{$url}{last_updated} ? strftime("%Y-%m-%d %H:%M:%S", localtime($source_metadata{$url}{last_updated})) : "Never";
    my $domains = $source_metadata{$url}{domains} // 0;
    my $license = $url_to_filename{$url}{comments} ? (split(/;/, $url_to_filename{$url}{comments}) )[0] : "Unknown";
    $license =~ s/License: //; # Extract only the license type
    $sources_md .= "| $url | $category | $last_updated | $domains | $license |\n";
}
open(my $sources_fh, '>', "$output_dir/SOURCES.md") or warn "Cannot write SOURCES.md: $!\n";
print $sources_fh $sources_md;
close $sources_fh;

# --- RPZ Validation ---
if ($validate) {
    my $validation = '';
    $validation .= "\n========== RPZ Validation ==========\n";
    my @rpz_files = glob("$output_dir/*/*.rpz");
    my $valid_count = 0;
    my $invalid_count = 0;
    my $total_domains_valid = 0;
    my $total_errors = 0;

    foreach my $file (@rpz_files) {
        open(my $fh, '<', $file) or do {
            $validation .= sprintf("%-30s : ERROR (cannot open)\n", $file);
            $invalid_count++;
            next;
        };
        my $ok = 1;
        my $domains = 0;
        my $errors = 0;
        my @error_lines;
        while (my $line = <$fh>) {
            chomp $line;
            next if $line =~ /^\s*($|[;#])/;
            if ($line =~ /^\$TTL/i || $line =~ /^\@ SOA /i || $line =~ /^\s+NS\s+/i) {
                next;
            }
            if ($line =~ /^([^\s]+)\s+CNAME\s+\.$/) {
                my $d = $1;
                unless (is_valid_domain($d)) {
                    push @error_lines, "Invalid domain: $d";
                    $ok = 0; $errors++;
                }
                $domains++;
                next;
            }
            if ($line =~ /^([^\s]+)\s+CNAME\s+rpz-drop\.$/) {
                my $d = $1;
                unless (is_valid_domain($d)) {
                    push @error_lines, "Invalid domain: $d";
                    $ok = 0; $errors++;
                }
                $domains++;
                next;
            }
            if ($line =~ /^\s*[#;]/) {
                next;
            }
            push @error_lines, "Invalid RPZ line: $line";
            $ok = 0; $errors++;
        }
        close $fh;
        $total_domains_valid += $domains;
        $total_errors += $errors;
        if ($ok) {
            $validation .= sprintf("%-30s : OK    (%5d domains)\n", basename($file), $domains);
            $valid_count++;
        } else {
            $validation .= sprintf("%-30s : ERROR (%5d domains, %d errors)\n", basename($file), $domains, $errors);
            $validation .= join("\n", map { "    -> $_" } @error_lines) . "\n";
            $invalid_count++;
        }
    }
    $validation .= "----------------------------------------------\n";
    $validation .= "Valid RPZ files  : $valid_count\n";
    $validation .= "Invalid RPZ files: $invalid_count\n";
    $validation .= "Total domains    : $total_domains_valid\n";
    $validation .= "Total errors     : $total_errors\n";
    $validation .= "==============================================\n";

    print $validation;

    if ($validation_report) {
        open(my $vrfh, '>', $validation_report) or warn "Cannot write validation report file '$validation_report': $!\n";
        print $vrfh $validation;
        close $vrfh;
    }
}

# --- Blocklist-to-RPZ conversion function ---
sub convert_blocklist_to_rpz {
    my ($content, $source_url, $wildcards, $no_soa, $comments) = @_;

    my $ttl        = 300;
    my $soa_serial = strftime("%Y%m%d00", localtime);
    my $soa        = "\@ SOA localhost. root.localhost. $soa_serial 43200 3600 86400 $ttl";
    my $ns         = "  NS  localhost.";

    my %seen;
    my $entry_count = 0;
    my @output_lines;

    sub is_valid_domain {
        my $d = shift;
        return 0 if $d =~ /^\d+\.\d+\.\d+\.\d+$/;
        return 0 if $d =~ /^\[?[a-fA-F0-9:.]+\]?$/;
        return $d =~ /^(?:\*\.)?([a-zA-Z0-9-]+\.)+[a-zA-Z]{2,}$/;
    }

    foreach my $line (split /\n/, $content) {
        chomp $line;
        $line =~ s/\r$//;
        $line =~ s/^\s+|\s+$//g;

        if ($line =~ /^\s*[#;]/) {
            $line =~ s/^#/;/;
            push @output_lines, "$line\n";
            next;
        }
        next if $line =~ /^\s*$/;

        my $domain;

        if ($line =~ /^\s*(?:0\.0\.0\.0|127\.0\.0\.1)\s+([^\s]+)/) {
            $domain = $1;
        }
        elsif ($line =~ /^\|\|([^\^]+)\^/) {
            $domain = $1;
        }
        elsif ($line =~ /^(\*?[^\s]+?\.[^\s]+?)\s*(?:[#;].*)?$/) {
            $domain = $1;
        }
        elsif ($line =~ /^(\*?[^\s]+?\.[^\s]+?)[,\t]/) {
            $domain = $1;
        }
        elsif ($line =~ m{^https?://(\*?[^\s]+?\.[^\s]+?)(?:/|$)}) {
            $domain = $1;
        }
        else {
            next;
        }

        my $is_wild = $domain =~ s/^\*\.//;

        next unless is_valid_domain($domain);
        next if $seen{$domain}++;
        push @output_lines, "$domain CNAME .\n";
        $entry_count++;
        if ($wildcards) {
            push @output_lines, "*.$domain CNAME .\n";
            $entry_count++;
        }
        elsif ($is_wild) {
            push @output_lines, "; (Wildcard entry ignored because --wildcards/-w not set)\n";
        }
    }

    my $header = '';
    $header .= "\$TTL $ttl\n";
    unless ($no_soa) {
        $header .= "$soa\n";
        $header .= "$ns\n";
    }
    $header .= ";\n";
    $header .= "; Generated by blocklist2rpz-multi.pl on " . scalar(localtime) . "\n";
    $header .= "; Source URL: $source_url\n";
    $header .= ";\n";
    if ($comments && $comments ne "No comments provided") {
        foreach my $comment_line (split /;/, $comments) {
            $comment_line =~ s/^\s+|\s+$//g;
            $header .= "; $comment_line\n" if $comment_line;
        }
        $header .= ";\n";
    }
    if ($source_url eq 'https://raw.githubusercontent.com/PolishFiltersTeam/KADhosts/master/KADhosts.txt') {
        $header .= "; Note: This RPZ file is licensed under CC BY-SA 4.0 as required by KADhosts\n";
        $header .= ";\n";
    }
    $header .= ";\n";
    $header .= "; ======================\n";
    $header .= "; Converted by: blocklist2rpz-multi (Perl script)\n";
    $header .= "; Source: $source_url\n";
    $header .= "; Wildcards: " . ($wildcards ? "enabled" : "disabled") . "\n";
    $header .= "; SOA/NS records: " . ($no_soa ? "disabled" : "enabled") . "\n";
    $header .= "; Number of entries: $entry_count\n";
    $header .= "; Conversion date: " . localtime() . "\n";
    $header .= "; ======================\n";
    $header .= ";\n";

    return ($header . join('', @output_lines), $entry_count);
}

# EOF
