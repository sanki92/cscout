#include <fstream>
#include <map>
#include <string>
#include <vector>
#include <set>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#include "swill.h"

#include "cpp.h"
#include "debug.h"
#include "error.h"
#include "parse.tab.h"
#include "attr.h"
#include "metrics.h"
#include "fileid.h"
#include "tokid.h"
#include "token.h"
#include "ptoken.h"
#include "fchar.h"
#include "pltoken.h"
#include "macro.h"
#include "pdtoken.h"
#include "eclass.h"
#include "type.h"
#include "stab.h"
#include "fdep.h"
#include "version.h"
#include "call.h"
#include "fcall.h"
#include "mcall.h"
#include "option.h"
#include "query.h"
#include "idquery.h"
#include "funquery.h"
#include "filequery.h"
#include "html.h"
#include "fileutils.h"
#include "globobj.h"
#include "filedetails.h"
#include "filemetrics.h"
#include "funmetrics.h"

#include "restapi.h"

#define ids Identifier::ids

static map<Eclass *, int> ec_to_eid;
static map<int, Eclass *> eid_to_ec;
static int next_eid = 1;

static map<Call *, int> call_to_id;
static map<int, Call *> id_to_call;
static int next_call_id = 1;

static bool id_maps_built = false;

static void
build_id_maps()
{
	if (id_maps_built)
		return;
	id_maps_built = true;

	for (IdProp::iterator i = ids.begin(); i != ids.end(); i++) {
		Eclass *e = i->first;
		if (ec_to_eid.find(e) == ec_to_eid.end()) {
			ec_to_eid[e] = next_eid;
			eid_to_ec[next_eid] = e;
			next_eid++;
		}
	}

	for (Call::const_fmap_iterator_type i = Call::fbegin();
	     i != Call::fend(); i++) {
		Call *c = i->second;
		if (call_to_id.find(c) == call_to_id.end()) {
			call_to_id[c] = next_call_id;
			id_to_call[next_call_id] = c;
			next_call_id++;
		}
	}
}

static int
get_eid(Eclass *e)
{
	map<Eclass *, int>::iterator it = ec_to_eid.find(e);
	if (it != ec_to_eid.end())
		return it->second;

	int id = next_eid++;
	ec_to_eid[e] = id;
	eid_to_ec[id] = e;
	return id;
}

static int
get_call_id(Call *c)
{
	map<Call *, int>::iterator it = call_to_id.find(c);
	if (it != call_to_id.end())
		return it->second;
	int id = next_call_id++;
	call_to_id[c] = id;
	id_to_call[id] = c;
	return id;
}


static string
json_escape(const string &s)
{
	string r;
	r.reserve(s.size() + 8);
	for (string::const_iterator i = s.begin(); i != s.end(); i++) {
		unsigned char c = static_cast<unsigned char>(*i);
		switch (c) {
		case '"':  r += "\\\""; break;
		case '\\': r += "\\\\"; break;
		case '\b': r += "\\b"; break;
		case '\f': r += "\\f"; break;
		case '\n': r += "\\n"; break;
		case '\r': r += "\\r"; break;
		case '\t': r += "\\t"; break;
		default:
			if (c < 0x20) {
				char buf[8];
				snprintf(buf, sizeof(buf), "\\u%04x", c);
				r += buf;
			} else {
				r += static_cast<char>(c);
			}
		}
	}
	return r;
}

static void
json_header(FILE *)
{
	swill_setheader("content-type", "application/json");
	swill_setheader("access-control-allow-origin", "*");
}

static bool
query_flag(const char *name)
{
	char *v = swill_getvar(name);
	if (!v)
		return false;
	return strcmp(v, "1") == 0 || strcmp(v, "true") == 0 || strcmp(v, "Y") == 0;
}

static int
query_int(const char *name, int default_value)
{
	char *v = swill_getvar(name);
	if (!v || !*v)
		return default_value;
	char *end = NULL;
	long n = strtol(v, &end, 10);
	if (end == v || *end != '\0' || n < 0)
		return default_value;
	if (n > 1000000)
		n = 1000000;
	return static_cast<int>(n);
}


static int
api_projects(FILE *of, void *)
{
	json_header(of);
	const Project::proj_map_type &pm = Project::get_project_map();

	fprintf(of, "[");
	bool first = true;
	for (Project::proj_map_type::const_iterator i = pm.begin();
	     i != pm.end(); i++) {
		if (!first) fprintf(of, ",");
		first = false;
		fprintf(of, "{\"pid\":%d,\"name\":\"%s\"}",
			i->second,
			json_escape(i->first).c_str());
	}
	fprintf(of, "]");
	return 0;
}

static int
api_project_files(FILE *of, void *)
{
	json_header(of);

	int pid;
	if (!swill_getargs("i(pid)", &pid)) {
		swill_setresponse("400 Bad Request");
		fprintf(of, "{\"error\":\"missing pid parameter\"}");
		return 0;
	}

	const Project::proj_map_type &pm = Project::get_project_map();
	bool valid = false;
	for (Project::proj_map_type::const_iterator i = pm.begin();
	     i != pm.end(); i++) {
		if (i->second == pid) {
			valid = true;
			break;
		}
	}
	if (!valid) {
		swill_setresponse("404 Not Found");
		fprintf(of, "{\"error\":\"unknown project id\"}");
		return 0;
	}

	vector<Fileid> files = Fileid::files(true);
	fprintf(of, "[");
	bool first = true;
	for (vector<Fileid>::iterator i = files.begin();
	     i != files.end(); i++) {
		if (!Filedetails::get_attribute(*i, pid))
			continue;
		if (!first) fprintf(of, ",");
		first = false;
		fprintf(of, "{\"fid\":%d,\"name\":\"%s\",\"readonly\":%s}",
			i->get_id(),
			json_escape(i->get_path()).c_str(),
			i->get_readonly() ? "true" : "false");
	}
	fprintf(of, "]");
	return 0;
}

static int
api_files(FILE *of, void *)
{
	json_header(of);
	vector<Fileid> files = Fileid::files(true);
	int limit = query_int("limit", -1);
	int offset = query_int("offset", 0);
	bool writable_only = query_flag("writable");
	int pid = query_int("pid", -1);

	if (pid >= 0) {
		const Project::proj_map_type &pm = Project::get_project_map();
		bool valid = false;
		for (Project::proj_map_type::const_iterator i = pm.begin(); i != pm.end(); i++) {
			if (i->second == pid) {
				valid = true;
				break;
			}
		}
		if (!valid) {
			swill_setresponse("404 Not Found");
			fprintf(of, "{\"error\":\"unknown project id\"}");
			return 0;
		}
	}

	int total = 0;
	for (vector<Fileid>::iterator i = files.begin();
	     i != files.end(); i++) {
		if (writable_only && i->get_readonly())
			continue;
		if (pid >= 0 && !Filedetails::get_attribute(*i, pid))
			continue;
		total++;
	}

	fprintf(of, "{\"total\":%d,\"items\":[", total);
	bool first = true;
	int seen = 0;
	int emitted = 0;
	for (vector<Fileid>::iterator i = files.begin();
	     i != files.end(); i++) {
		if (writable_only && i->get_readonly())
			continue;
		if (pid >= 0 && !Filedetails::get_attribute(*i, pid))
			continue;
		if (seen++ < offset)
			continue;
		if (limit >= 0 && emitted >= limit)
			break;
		if (!first) fprintf(of, ",");
		first = false;
		emitted++;
		fprintf(of, "{\"fid\":%d,\"name\":\"%s\",\"readonly\":%s}",
			i->get_id(),
			json_escape(i->get_path()).c_str(),
			i->get_readonly() ? "true" : "false");
	}
	fprintf(of, "]}");
	return 0;
}

static int
api_file_metrics(FILE *of, void *)
{
	json_header(of);

	int fid;
	if (!swill_getargs("i(fid)", &fid)) {
		swill_setresponse("400 Bad Request");
		fprintf(of, "{\"error\":\"missing fid parameter\"}");
		return 0;
	}

	if (fid < 0 || fid > Fileid::max_id()) {
		swill_setresponse("404 Not Found");
		fprintf(of, "{\"error\":\"fid out of range\"}");
		return 0;
	}

	Fileid fi(fid);
	const FileMetrics &m = Filedetails::get_pre_cpp_metrics(fi);

	fprintf(of, "{\"fid\":%d,\"name\":\"%s\",\"metrics\":{",
		fid,
		json_escape(fi.get_path()).c_str());

	bool first = true;
	for (int j = 0; j < FileMetrics::metric_max; j++) {
		if (Metrics::is_internal<FileMetrics>(j))
			continue;
		const string mname = Metrics::get_name<FileMetrics>(j);
		if (mname.empty())
			continue;
		if (!first) fprintf(of, ",");
		first = false;
		double val = m.get_metric(j);
		fprintf(of, "\"%s\":%.10g",
			json_escape(mname).c_str(),
			val);
	}
	fprintf(of, "}}");
	return 0;
}

static int
api_identifiers(FILE *of, void *)
{
	json_header(of);
	build_id_maps();

	bool filter_unused = query_flag("unused");
	bool filter_writable = query_flag("writable");
	int limit = query_int("limit", -1);
	int offset = query_int("offset", 0);

	int total = 0;
	for (IdProp::iterator i = ids.begin(); i != ids.end(); i++) {
		Eclass *e = i->first;
		if (filter_unused && !e->is_unused())
			continue;
		if (filter_writable && e->get_attribute(is_readonly))
			continue;
		total++;
	}

	fprintf(of, "{\"total\":%d,\"items\":[", total);
	bool first = true;
	int seen = 0;
	int emitted = 0;
	for (IdProp::iterator i = ids.begin(); i != ids.end(); i++) {
		Eclass *e = i->first;
		Identifier &id = i->second;

		bool is_unused = e->is_unused();
		bool is_ro = e->get_attribute(is_readonly);

		if (filter_unused && !is_unused)
			continue;
		if (filter_writable && is_ro)
			continue;
		if (seen++ < offset)
			continue;
		if (limit >= 0 && emitted >= limit)
			break;

		if (!first) fprintf(of, ",");
		first = false;
		emitted++;

		fprintf(of,
			"{\"eid\":%d"
			",\"name\":\"%s\""
			",\"readonly\":%s"
			",\"unused\":%s"
			",\"macro\":%s"
			",\"macroarg\":%s"
			",\"ordinary\":%s"
			",\"suetag\":%s"
			",\"sumember\":%s"
			",\"label\":%s"
			",\"typedef\":%s"
			",\"enumeration\":%s"
			",\"yacc\":%s"
			",\"fun\":%s"
			",\"cscope\":%s"
			",\"lscope\":%s"
			",\"xfile\":%s}",
			get_eid(e),
			json_escape(id.get_id()).c_str(),
			is_ro ? "true" : "false",
			is_unused ? "true" : "false",
			e->get_attribute(is_macro) ? "true" : "false",
			e->get_attribute(is_macro_arg) ? "true" : "false",
			e->get_attribute(is_ordinary) ? "true" : "false",
			e->get_attribute(is_suetag) ? "true" : "false",
			e->get_attribute(is_sumember) ? "true" : "false",
			e->get_attribute(is_label) ? "true" : "false",
			e->get_attribute(is_typedef) ? "true" : "false",
			e->get_attribute(is_enumeration) ? "true" : "false",
			e->get_attribute(is_yacc) ? "true" : "false",
			e->get_attribute(is_cfunction) ? "true" : "false",
			e->get_attribute(is_cscope) ? "true" : "false",
			e->get_attribute(is_lscope) ? "true" : "false",
			id.get_xfile() ? "true" : "false");
	}
	fprintf(of, "]}");
	return 0;
}

static int
api_identifier(FILE *of, void *)
{
	json_header(of);
	build_id_maps();

	int eid;
	if (!swill_getargs("i(eid)", &eid)) {
		swill_setresponse("400 Bad Request");
		fprintf(of, "{\"error\":\"missing eid parameter\"}");
		return 0;
	}

	map<int, Eclass *>::iterator it = eid_to_ec.find(eid);
	if (it == eid_to_ec.end()) {
		swill_setresponse("404 Not Found");
		fprintf(of, "{\"error\":\"unknown eid\"}");
		return 0;
	}

	Eclass *e = it->second;
	IdProp::iterator idi = ids.find(e);
	if (idi == ids.end()) {
		swill_setresponse("404 Not Found");
		fprintf(of, "{\"error\":\"identifier not found\"}");
		return 0;
	}

	Identifier &id = idi->second;

	fprintf(of,
		"{\"eid\":%d"
		",\"name\":\"%s\""
		",\"unused\":%s"
		",\"xfile\":%s"
		",\"locations\":[",
		eid,
		json_escape(id.get_id()).c_str(),
		e->is_unused() ? "true" : "false",
		id.get_xfile() ? "true" : "false");

	const setTokid &members = e->get_members();
	bool first = true;
	for (setTokid::const_iterator mi = members.begin();
	     mi != members.end(); mi++) {
		Fileid fi = mi->get_fileid();
		int line = Filedetails::get_line_number(fi, mi->get_streampos());

		if (!first) fprintf(of, ",");
		first = false;
		fprintf(of,
			"{\"fid\":%d"
			",\"file\":\"%s\""
			",\"line\":%d"
			",\"offset\":%ld}",
			fi.get_id(),
			json_escape(fi.get_path()).c_str(),
			line,
			(long)mi->get_streampos());
	}

	fprintf(of, "]}");
	return 0;
}

static int
api_functions(FILE *of, void *)
{
	json_header(of);
	build_id_maps();
	bool defined_only = query_flag("defined");
	int limit = query_int("limit", -1);
	int offset = query_int("offset", 0);

	int total = 0;
	for (Call::const_fmap_iterator_type i = Call::fbegin();
	     i != Call::fend(); i++) {
		if (defined_only && !i->second->is_defined())
			continue;
		total++;
	}

	fprintf(of, "{\"total\":%d,\"items\":[", total);
	bool first = true;
	int seen = 0;
	int emitted = 0;
	for (Call::const_fmap_iterator_type i = Call::fbegin();
	     i != Call::fend(); i++) {
		Call *c = i->second;
		if (defined_only && !c->is_defined())
			continue;
		if (seen++ < offset)
			continue;
		if (limit >= 0 && emitted >= limit)
			break;
		if (!first) fprintf(of, ",");
		first = false;
		emitted++;

		fprintf(of,
			"{\"id\":%d"
			",\"name\":\"%s\""
			",\"is_macro\":%s"
			",\"is_defined\":%s"
			",\"is_declared\":%s"
			",\"is_file_scoped\":%s"
			",\"fid\":%d"
			",\"fanin\":%d"
			",\"fanout\":%d}",
			get_call_id(c),
			json_escape(c->get_name()).c_str(),
			c->is_macro() ? "true" : "false",
			c->is_defined() ? "true" : "false",
			c->is_declared() ? "true" : "false",
			c->is_file_scoped() ? "true" : "false",
			c->get_fileid().get_id(),
			c->get_num_caller(),
			c->get_num_call());
	}
	fprintf(of, "]}");
	return 0;
}

static Call *
lookup_call(FILE *of, const char *param)
{
	build_id_maps();
	int id;
	if (!swill_getargs("i(id)", &id)) {
		swill_setresponse("400 Bad Request");
		fprintf(of, "{\"error\":\"missing id parameter\"}");
		return NULL;
	}
	map<int, Call *>::iterator it = id_to_call.find(id);
	if (it == id_to_call.end()) {
		swill_setresponse("404 Not Found");
		fprintf(of, "{\"error\":\"unknown function id\"}");
		return NULL;
	}
	return it->second;
}

static int
api_function(FILE *of, void *)
{
	json_header(of);
	Call *f = lookup_call(of, "id");
	if (!f) return 0;

	fprintf(of,
		"{\"id\":%d"
		",\"name\":\"%s\""
		",\"is_macro\":%s"
		",\"is_defined\":%s"
		",\"is_declared\":%s"
		",\"is_file_scoped\":%s"
		",\"fid\":%d"
		",\"fanin\":%d"
		",\"fanout\":%d}",
		get_call_id(f),
		json_escape(f->get_name()).c_str(),
		f->is_macro() ? "true" : "false",
		f->is_defined() ? "true" : "false",
		f->is_declared() ? "true" : "false",
		f->is_file_scoped() ? "true" : "false",
		f->get_fileid().get_id(),
		f->get_num_caller(),
		f->get_num_call());
	return 0;
}

static int
api_function_callers(FILE *of, void *)
{
	json_header(of);
	Call *f = lookup_call(of, "id");
	if (!f) return 0;

	fprintf(of, "[");
	bool first = true;
	for (Call::const_fiterator_type ci = f->caller_begin();
	     ci != f->caller_end(); ci++) {
		if (!first) fprintf(of, ",");
		first = false;
		fprintf(of, "{\"id\":%d,\"name\":\"%s\"}",
			get_call_id(*ci),
			json_escape((*ci)->get_name()).c_str());
	}
	fprintf(of, "]");
	return 0;
}

static int
api_function_callees(FILE *of, void *)
{
	json_header(of);
	Call *f = lookup_call(of, "id");
	if (!f) return 0;

	fprintf(of, "[");
	bool first = true;
	for (Call::const_fiterator_type ci = f->call_begin();
	     ci != f->call_end(); ci++) {
		if (!first) fprintf(of, ",");
		first = false;
		fprintf(of, "{\"id\":%d,\"name\":\"%s\"}",
			get_call_id(*ci),
			json_escape((*ci)->get_name()).c_str());
	}
	fprintf(of, "]");
	return 0;
}

static int
api_source(FILE *of, void *)
{
	json_header(of);

	int fid;
	if (!swill_getargs("i(fid)", &fid)) {
		swill_setresponse("400 Bad Request");
		fprintf(of, "{\"error\":\"missing fid parameter\"}");
		return 0;
	}

	if (fid < 0 || fid > Fileid::max_id()) {
		swill_setresponse("404 Not Found");
		fprintf(of, "{\"error\":\"fid out of range\"}");
		return 0;
	}

	Fileid fi(fid);
	ifstream src(fi.get_path().c_str());
	if (!src.is_open()) {
		swill_setresponse("404 Not Found");
		fprintf(of, "{\"error\":\"file not readable\"}");
		return 0;
	}

	fprintf(of, "{\"fid\":%d,\"name\":\"%s\",\"lines\":[",
		fid, json_escape(fi.get_path()).c_str());

	string line;
	bool first = true;
	while (getline(src, line)) {
		if (!line.empty() && line[line.size() - 1] == '\r')
			line.erase(line.size() - 1);
		if (!first) fprintf(of, ",");
		first = false;
		fprintf(of, "\"%s\"", json_escape(line).c_str());
	}

	fprintf(of, "]}");
	return 0;
}

void
rest_api_register()
{
	build_id_maps();

	swill_handle("api/projects", api_projects, NULL);
	swill_handle("api/project_files", api_project_files, NULL);
	swill_handle("api/files", api_files, NULL);
	swill_handle("api/filemetrics", api_file_metrics, NULL);
	swill_handle("api/identifiers", api_identifiers, NULL);
	swill_handle("api/identifier", api_identifier, NULL);
	swill_handle("api/functions", api_functions, NULL);
	swill_handle("api/function", api_function, NULL);
	swill_handle("api/function_callers", api_function_callers, NULL);
	swill_handle("api/function_callees", api_function_callees, NULL);
	swill_handle("api/source", api_source, NULL);
}
