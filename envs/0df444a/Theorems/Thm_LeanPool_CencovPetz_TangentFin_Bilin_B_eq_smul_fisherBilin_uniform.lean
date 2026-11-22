-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_TangentFin_Bilin_B_eq_smul_fisherBilin_uniform
-- name    : LeanPool.CencovPetz.TangentFin.Bilin.B_eq_smul_fisherBilin_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:48.696237+00:00
-- url     : https://prove2.me/theorems/180ef3b9-08ff-4574-a3e6-06947789fc7f
-- title:
--   Bilin: B eq smul fisher Bilin uniform
-- statement:
--   The Bilin construction uses the B eq smul fisher Bilin uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/UniformScalarMultiple.lean#L366-L412
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/UniformScalarMultiple.lean#L366-L412

module
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariantBilinForm
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Definitions.Def_LeanPool_CencovPetz_UniformScalarMultiple
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
open LeanPool.CencovPetz.TangentFin
open LeanPool.CencovPetz.TangentFin.Bilin
open _root_.LeanPool.CencovPetz.TangentFin.Basis
variable {n : ℕ} (G : MonotoneMetricFamily) [Nonempty (Fin n)]

theorem LeanPool.CencovPetz.TangentFin.Bilin.B_eq_smul_fisherBilin_uniform (i0 i1 : Fin n) (hi01 : i0 ≠ i1) :
  B (G := G) (n := n)
    =
      (B (G := G) (n := n) (dij (n := n) i0 i1) (dij (n := n) i0 i1) /
          (2 * (Fintype.card (Fin n) : ℝ))) • fisherBilin (Simplex.uniform (α := Fin n)) := by sorry
