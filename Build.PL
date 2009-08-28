use warnings;
use strict;

use Module::Build;

Module::Build->new(
	module_name => "Sub::Filter",
	dist_version => "0.000",
	license => "perl",
	build_requires => {
		"ExtUtils::CBuilder" => "0.15",
		"Module::Build" => 0,
		"Sub::Mutate" => 0,
		"Test::More" => 0,
		"perl" => "5.006001",
		"strict" => 0,
		"warnings" => 0,
	},
	requires => {
		"Attribute::Lexical" => 0,
		"Carp" => 0,
		"Sub::Mutate" => 0,
		"XSLoader" => 0,
		"perl" => "5.006001",
		"strict" => 0,
		"warnings" => 0,
	},
	dynamic_config => 0,
	meta_add => { distribution_type => "module" },
	create_makefile_pl => "passthrough",
	sign => 1,
)->create_build_script;

exit 0;
