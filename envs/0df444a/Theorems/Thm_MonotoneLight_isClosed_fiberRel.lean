-- Prove2me | Theorems.Thm_MonotoneLight_isClosed_fiberRel
-- name    : MonotoneLight.isClosed_fiberRel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:17.336598+00:00
-- url     : https://prove2.me/theorems/73017eb4-512e-51f8-978a-79560d569866
-- title:
--   Monotone Light: is Closed fiber Rel
-- statement:
--   The fiber-component equivalence relation is closed.
--
--   Source: https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L103-L113
-- source:
--   https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L103-L113

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

theorem MonotoneLight.isClosed_fiberRel [_cX : CompactSpace X] [_hX : T2Space X] [_hY : T2Space Y]
    {f : X → Y} (hf : Continuous f) : IsClosed {p : X × X | FiberRel f p.1 p.2} := by sorry
