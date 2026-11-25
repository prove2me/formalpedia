-- Prove2me | Theorems.Thm_NonCutPoints_eq_of_contains_noncut_points
-- name    : NonCutPoints.eq_of_contains_noncut_points
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:33:35.106399+00:00
-- url     : https://prove2.me/theorems/f6429d2e-afbc-44a4-80fa-52052fa579f5
-- title:
--   Non Cut Points: eq of contains noncut points
-- statement:
--   A compact connected subset containing every non-cut point of a compact
--   connected Hausdorff set equals that set. This also holds when the ambient
--   connected set is a singleton.
--
--   Source: https://github.com/Arthur742Ramos/non-cut-points-lean/blob/b1d0ed0338d098a4c84622828390cc84027df8dc/Solution.lean#L340-L359
-- source:
--   https://github.com/Arthur742Ramos/non-cut-points-lean/blob/b1d0ed0338d098a4c84622828390cc84027df8dc/Solution.lean#L340-L359

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

theorem NonCutPoints.eq_of_contains_noncut_points [t2X : T2Space X] {C K : Set X}
    (hCcompact : IsCompact C) (hCconnected : IsConnected C)
    (_hKcompact : IsCompact K) (hKconnected : IsConnected K) (hKC : K ⊆ C)
    (hcontains : ∀ x, IsNonCutPoint C x → x ∈ K) : K = C := by sorry
