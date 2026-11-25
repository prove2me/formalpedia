-- Prove2me | Theorems.Thm_MonotoneLight_surjective_monotone
-- name    : MonotoneLight.surjective_monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:21.385799+00:00
-- url     : https://prove2.me/theorems/01a015bf-fee4-4752-a475-5ba1981df82e
-- title:
--   Monotone Light: surjective monotone
-- statement:
--   The Monotone Light construction uses the surjective monotone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L130-L131
-- source:
--   https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L130-L131

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

theorem MonotoneLight.surjective_monotone (f : X → Y) : Surjective (monotone f) := by sorry
