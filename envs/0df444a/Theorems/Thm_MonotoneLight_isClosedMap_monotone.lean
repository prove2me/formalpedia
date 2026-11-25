-- Prove2me | Theorems.Thm_MonotoneLight_isClosedMap_monotone
-- name    : MonotoneLight.isClosedMap_monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:30.05609+00:00
-- url     : https://prove2.me/theorems/f5673e59-8524-5846-978f-6a9e148d2ac0
-- title:
--   Monotone Light: is Closed Map monotone
-- statement:
--   The Monotone Light construction uses the is Closed Map monotone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L133-L149
-- source:
--   https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L133-L149

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

theorem MonotoneLight.isClosedMap_monotone [_cX : CompactSpace X] [_hX : T2Space X] [_hY : T2Space Y]
    {f : X → Y} (hf : Continuous f) : IsClosedMap (monotone f) := by sorry
