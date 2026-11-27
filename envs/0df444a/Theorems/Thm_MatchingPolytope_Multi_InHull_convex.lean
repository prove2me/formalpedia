-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_InHull_convex
-- name    : MatchingPolytope.Multi.InHull.convex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:49.542988+00:00
-- url     : https://prove2.me/theorems/b2e01019-a032-4d13-a2b8-96ea8a01b79f
-- title:
--   In Hull: convex
-- statement:
--   The In Hull construction uses the convex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L280-L294
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L280-L294

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
variable [Fintype E]

theorem MatchingPolytope.Multi.InHull.convex {Q : Finset E → Prop} {x y : E → ℝ} (hx : InHull Q x) (hy : InHull Q y)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : InHull Q (a • x + b • y) := by sorry
