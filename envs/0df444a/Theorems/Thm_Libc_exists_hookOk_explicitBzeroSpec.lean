-- Prove2me | Theorems.Thm_Libc_exists_hookOk_explicitBzeroSpec
-- name    : Libc.exists_hookOk_explicitBzeroSpec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-24T17:23:30.958551+00:00
-- url     : https://prove2.me/theorems/b0568888-23ef-4056-9fcd-58e4cb7e3812
-- title:
--   The explicit_bzero hook contract can be met — some hook satisfies HookOk for explicitBzeroSpec
-- statement:
--   There is a hook $f$ (a function from machine states to machine states) with `HookOk f Libc.explicitBzeroSpec`. So a theorem that assumes `HookOk f Libc.explicitBzeroSpec` for its `explicit_bzero` or `sodium_memzero` hook does not hold vacuously. A witness: write `x1` zero bytes at the address in `x0`, then continue at the address in `x30`.
-- source:
--   explicit_bzero: The GNU C Library Reference Manual, "Erasing Sensitive Data", https://sourceware.org/glibc/manual/latest/html_node/Erasing-Sensitive-Data.html, and the OpenBSD manual page bzero(3), https://man.openbsd.org/explicit_bzero.3, non-vacuity of the explicit_bzero hook contract: a hook that zeroes the bytes and returns meets it

import Definitions.Def_Libc_ExplicitBzero

open Arm64

namespace Libc

theorem exists_hookOk_explicitBzeroSpec :
    ∃ f : State → State, HookOk f explicitBzeroSpec := by
  sorry

end Libc
