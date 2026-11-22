-- Prove2me | Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
-- name    : LLexpr.SupLinearCombination.eval_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:20.125885+00:00
-- url     : https://prove2.me/theorems/c317b7a3-0c72-4c55-bd16-705b881df499
-- title:
--   Sup Linear Combination: eval singleton
-- statement:
--   Evaluating a singleton supremum gives the corresponding linear combination.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L191-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L191-L194

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
open LLexpr.SupLinearCombination

theorem LLexpr.SupLinearCombination.eval_singleton {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (a : Fin n → ℝ) (x : Fin n → X) :
    (singleton a).eval x = Fintype.linearCombination ℝ x a := by sorry
