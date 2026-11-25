-- Prove2me | Theorems.Thm_MonotoneLight_middle_t2Space
-- name    : MonotoneLight.middle_t2Space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:19.942811+00:00
-- url     : https://prove2.me/theorems/d495df09-7640-5d90-bcb3-93244bf632f2
-- title:
--   Monotone Light: middle t2 Space
-- statement:
--   The fiber-component quotient of a compact Hausdorff space is Hausdorff.
--
--   Source: https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L152-L176
-- source:
--   https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L152-L176

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

theorem MonotoneLight.middle_t2Space [_cX : CompactSpace X] [_hX : T2Space X] [_hY : T2Space Y]
    {f : X → Y} (hf : Continuous f) : T2Space (Middle f) := by sorry
