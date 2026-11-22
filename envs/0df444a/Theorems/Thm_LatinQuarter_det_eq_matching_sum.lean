-- Prove2me | Theorems.Thm_LatinQuarter_det_eq_matching_sum
-- name    : LatinQuarter.det_eq_matching_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:56.186267+00:00
-- url     : https://prove2.me/theorems/2388b347-741a-4117-ad0b-79950d7a5433
-- title:
--   Latin Quarter: det eq matching sum
-- statement:
--   In characteristic two the determinant is exactly the unsigned
--   matching sum, written with a choice in each selected row.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Rows.lean#L85-L96
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Rows.lean#L85-L96

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.CharP.Two
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Definitions.Def_LeanPool_LatinQuarter_Rows
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix

theorem LatinQuarter.det_eq_matching_sum {R ι : Type*} [CommRing R] [CharP R 2]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    M.det = ∑ σ : Equiv.Perm ι, ∏ i, M i (σ i) := by sorry
