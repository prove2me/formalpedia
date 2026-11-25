-- Prove2me | Theorems.Thm_OpenMath_dist_getVert_of_geodesic
-- name    : OpenMath.dist_getVert_of_geodesic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:36:56.357965+00:00
-- url     : https://prove2.me/theorems/d560d450-2d75-4fb5-a8ec-0a952ef21441
-- title:
--   Open Math: dist get Vert of geodesic
-- statement:
--   Vertices along a shortest walk are at the expected distances from both ends.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Common.lean#L82-L93
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Common.lean#L82-L93

module
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Data.Real.Basic
public import Definitions.Def_OpenMath_Common
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath
open SimpleGraph Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem OpenMath.dist_getVert_of_geodesic {G : SimpleGraph α} (h : G.Connected) {u w : α}
    (p : G.Walk u w) (hp : p.length = G.dist u w) {i : ℕ} (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i ∧ G.dist (p.getVert i) w = p.length - i := by sorry
