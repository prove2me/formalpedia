-- Prove2me | Theorems.Thm_NonCutPoints_exists_two_noncut_points
-- name    : NonCutPoints.exists_two_noncut_points
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:33:43.074149+00:00
-- url     : https://prove2.me/theorems/30f81d6c-3528-400a-9e45-f82b6fcb837a
-- title:
--   Non Cut Points: exists two noncut points
-- statement:
--   A nontrivial compact connected Hausdorff set has two distinct points
--   whose individual removals leave connected sets.
--
--   Source: https://github.com/Arthur742Ramos/non-cut-points-lean/blob/b1d0ed0338d098a4c84622828390cc84027df8dc/Solution.lean#L324-L335
-- source:
--   https://github.com/Arthur742Ramos/non-cut-points-lean/blob/b1d0ed0338d098a4c84622828390cc84027df8dc/Solution.lean#L324-L335

module
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Order.Zorn
public import Definitions.Def_NonCutPoints_Solution
set_option autoImplicit true
@[expose] public section
public section
open Set
universe u
open NonCutPoints
variable {X : Type u} [tX : TopologicalSpace X]

theorem NonCutPoints.exists_two_noncut_points [t2X : T2Space X] {C : Set X}
    (hCcompact : IsCompact C) (hCconnected : IsConnected C) (hCnontrivial : C.Nontrivial) :
    ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ IsConnected (C \ {x}) ∧ IsConnected (C \ {y}) := by sorry
