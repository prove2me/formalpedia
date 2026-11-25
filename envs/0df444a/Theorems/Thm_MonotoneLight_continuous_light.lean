-- Prove2me | Theorems.Thm_MonotoneLight_continuous_light
-- name    : MonotoneLight.continuous_light
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:23.949298+00:00
-- url     : https://prove2.me/theorems/530a6792-694f-5d92-b165-c8c34b4ff8f3
-- title:
--   Monotone Light: continuous light
-- statement:
--   The Monotone Light construction uses the continuous light property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L186-L187
-- source:
--   https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L186-L187

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

theorem MonotoneLight.continuous_light {f : X → Y} (hf : Continuous f) : Continuous (light f) := by sorry
