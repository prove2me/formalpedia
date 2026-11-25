-- Prove2me | Theorems.Thm_MonotoneLight_totallyDisconnected_light_fiber
-- name    : MonotoneLight.totallyDisconnected_light_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:41:21.169718+00:00
-- url     : https://prove2.me/theorems/74ee4933-4a04-51fd-8647-6e2b04115db1
-- title:
--   Monotone Light: totally Disconnected light fiber
-- statement:
--   The Monotone Light construction uses the totally Disconnected light fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L205-L225
-- source:
--   https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L205-L225

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

theorem MonotoneLight.totallyDisconnected_light_fiber [_cX : CompactSpace X] [_hX : T2Space X] [_hY : T2Space Y]
    {f : X → Y} (hf : Continuous f) (y : Y) :
    IsTotallyDisconnected (light f ⁻¹' {y}) := by sorry
