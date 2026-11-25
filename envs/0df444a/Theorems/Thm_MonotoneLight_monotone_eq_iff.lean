-- Prove2me | Theorems.Thm_MonotoneLight_monotone_eq_iff
-- name    : MonotoneLight.monotone_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:10.047318+00:00
-- url     : https://prove2.me/theorems/cd6fe23c-4a0b-466c-ac8e-58711a6d303e
-- title:
--   Monotone Light: monotone eq iff
-- statement:
--   The Monotone Light construction uses the monotone eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L122-L123
-- source:
--   https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L122-L123

module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Definitions.Def_MonotoneLight_Solution
set_option autoImplicit true
@[expose] public section
public section
open Set Function Topology
universe u v
open MonotoneLight
variable {X : Type u} {Y : Type v} [_tX : TopologicalSpace X] [_tY : TopologicalSpace Y]
omit [TopologicalSpace Y]

theorem MonotoneLight.monotone_eq_iff {f : X → Y} {x y : X} :
    monotone f x = monotone f y ↔ FiberRel f x y := by sorry
