-- Prove2me | Theorems.Thm_MonotoneLight_continuous_monotone
-- name    : MonotoneLight.continuous_monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:38.292106+00:00
-- url     : https://prove2.me/theorems/948a1e22-ad7e-4525-97ce-d198284a35e6
-- title:
--   Monotone Light: continuous monotone
-- statement:
--   The Monotone Light construction uses the continuous monotone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L126-L127
-- source:
--   https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L126-L127

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

theorem MonotoneLight.continuous_monotone (f : X → Y) : Continuous (monotone f) := by sorry
