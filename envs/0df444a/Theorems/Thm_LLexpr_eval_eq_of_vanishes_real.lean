-- Prove2me | Theorems.Thm_LLexpr_eval_eq_of_vanishes_real
-- name    : LLexpr.eval_eq_of_vanishes_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:11.640945+00:00
-- url     : https://prove2.me/theorems/99ce648c-f072-4a54-bfa7-181e7f002dd1
-- title:
--   LLexpr: eval eq of vanishes real
-- statement:
--   If the difference of two formal expressions vanishes on the reals, their
--   evaluations agree in every vector lattice.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L502-L509
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L502-L509

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
set_option autoImplicit true
@[expose] public section
public section
open LLexpr
open scoped BigOperators
variable {n : ℕ}

theorem LLexpr.eval_eq_of_vanishes_real {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (x : Fin n → X) (e₁ e₂ : LLexpr n)
    (h : Vanishes ℝ (add e₁ (smul (-1) e₂))) :
    eval x e₁ = eval x e₂ := by sorry
