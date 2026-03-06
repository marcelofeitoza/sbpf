mod utils;

use {
    std::process::Command,
    utils::{
        TestEnv, init_project, run_build, update_assembly_file, verify_project_structure,
        verify_so_files, write_include_file,
    },
};

#[test]
fn test_macro_simple() {
    let env = TestEnv::new("macro_simple");

    init_project(&env, "macro_simple");
    verify_project_structure(&env, "macro_simple");

    update_assembly_file(
        &env,
        "macro_simple",
        r#".globl entrypoint
.macro do_nothing
.endm

.text
entrypoint:
  do_nothing
  mov64 r0, 0
  exit
"#,
    );

    run_build(&env);
    verify_so_files(&env);

    env.cleanup();
}

#[test]
fn test_macro_with_args() {
    let env = TestEnv::new("macro_args");

    init_project(&env, "macro_args");
    verify_project_structure(&env, "macro_args");

    update_assembly_file(
        &env,
        "macro_args",
        r#".globl entrypoint
.macro log_msg msg_addr, len
    lddw r1, \msg_addr
    lddw r2, \len
    call sol_log_
    exit
.endm

.text
entrypoint:
  call log_hello
  mov64 r0, 0
  exit

log_hello:
  log_msg hello_msg, 13
  exit

.rodata
hello_msg: .ascii "Hello, macro!"
"#,
    );

    run_build(&env);
    verify_so_files(&env);

    env.cleanup();
}

#[test]
fn test_macro_duplicate_fails() {
    let env = TestEnv::new("macro_dup");

    init_project(&env, "macro_dup");
    verify_project_structure(&env, "macro_dup");

    update_assembly_file(
        &env,
        "macro_dup",
        r#".globl entrypoint
.macro foo
  mov64 r0, 0
.endm
.macro foo
  mov64 r0, 1
.endm

.text
entrypoint:
  foo
  exit
"#,
    );

    let output = Command::new(&env.sbpf_bin)
        .current_dir(&env.project_dir)
        .arg("build")
        .output()
        .expect("Failed to run sbpf build");

    assert!(
        !output.status.success(),
        "Build should fail on duplicate macro"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Duplicate macro") || stderr.contains("duplicate"),
        "Error should mention duplicate macro: {}",
        stderr
    );

    env.cleanup();
}

#[test]
fn test_macro_arg_count_mismatch_fails() {
    let env = TestEnv::new("macro_arg_mismatch");

    init_project(&env, "macro_arg_mismatch");
    verify_project_structure(&env, "macro_arg_mismatch");

    update_assembly_file(
        &env,
        "macro_arg_mismatch",
        r#".globl entrypoint
.macro two_args a, b
  mov64 r0, 0
.endm

.text
entrypoint:
  two_args 1
  exit
"#,
    );

    let output = Command::new(&env.sbpf_bin)
        .current_dir(&env.project_dir)
        .arg("build")
        .output()
        .expect("Failed to run sbpf build");

    assert!(
        !output.status.success(),
        "Build should fail on arg count mismatch"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("expects") && stderr.contains("argument"),
        "Error should mention argument count: {}",
        stderr
    );

    env.cleanup();
}

#[test]
fn test_macro_with_include() {
    let env = TestEnv::new("macro_include");

    init_project(&env, "macro_include");
    verify_project_structure(&env, "macro_include");

    write_include_file(
        &env,
        "macro_include",
        "macros.s",
        r#".macro log_str msg, len
    lddw r1, \msg
    lddw r2, \len
    call sol_log_
    exit
.endm
"#,
    );

    update_assembly_file(
        &env,
        "macro_include",
        r#".globl entrypoint
.include "macros.s"
.text
entrypoint:
  call do_log
  mov64 r0, 0
  exit

do_log:
  log_str msg, 11
  exit

.rodata
msg: .ascii "Macros work"
"#,
    );

    run_build(&env);
    verify_so_files(&env);

    env.cleanup();
}
