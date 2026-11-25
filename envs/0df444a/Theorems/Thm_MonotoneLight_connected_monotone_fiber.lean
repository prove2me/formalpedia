-- Prove2me | Theorems.Thm_MonotoneLight_connected_monotone_fiber
-- name    : MonotoneLight.connected_monotone_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:35.436742+00:00
-- url     : https://prove2.me/theorems/9679217e-1c4e-433c-a00d-dca36db5d0b9
-- title:
--   Monotone Light: connected monotone fiber
-- statement:
--   The Monotone Light construction uses the connected monotone fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L196-L203
-- source:
--   https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L196-L203

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

theorem MonotoneLight.connected_monotone_fiber (f : X → Y) (z : Middle f) :
    IsConnected (monotone f ⁻¹' {z}) := by sorry
