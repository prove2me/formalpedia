-- Prove2me | Theorems.Thm_LLexpr_NormalForm_eval_var
-- name    : LLexpr.NormalForm.eval_var
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:28.416746+00:00
-- url     : https://prove2.me/theorems/387298e7-0e0a-4433-8d8f-40c9456ae8ff
-- title:
--   Normal Form: eval var
-- statement:
--   Evaluating a variable normal form gives the corresponding tuple entry.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L425-L428
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L425-L428

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

theorem LLexpr.NormalForm.eval_var {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (i : Fin n) (x : Fin n → X) :
    (var i).eval x = x i := by sorry
