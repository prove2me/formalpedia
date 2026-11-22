-- Prove2me | Theorems.Thm_LLexpr_NormalForm_eval_smul
-- name    : LLexpr.NormalForm.eval_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:34.750881+00:00
-- url     : https://prove2.me/theorems/b1bb7cb5-e363-47fb-963d-86bb805b5b88
-- title:
--   Normal Form: eval smul
-- statement:
--   Evaluation turns scalar multiplication of normal forms into scalar multiplication.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L445-L453
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L445-L453

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
open LLexpr.NormalForm

theorem LLexpr.NormalForm.eval_smul {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (r : ℝ) (N : NormalForm n)
    (x : Fin n → X) :
    (smul r N).eval x = r • N.eval x := by sorry
