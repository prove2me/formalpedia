-- Prove2me | Theorems.Thm_MonotoneLight_surjective_light
-- name    : MonotoneLight.surjective_light
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:31.195312+00:00
-- url     : https://prove2.me/theorems/47d481b8-51a6-5b46-97a0-1f7ee11c8000
-- title:
--   Monotone Light: surjective light
-- statement:
--   The Monotone Light construction uses the surjective light property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L190-L193
-- source:
--   https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L190-L193

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

theorem MonotoneLight.surjective_light {f : X → Y} (hf : Surjective f) : Surjective (light f) := by sorry
