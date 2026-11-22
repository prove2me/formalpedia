-- Prove2me | Theorems.Thm_LatinQuarter_allMinorsIn_mul_left
-- name    : LatinQuarter.allMinorsIn_mul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:30.250947+00:00
-- url     : https://prove2.me/theorems/38c478da-5f09-4e8d-87a5-e143a7bd6ede
-- title:
--   Latin Quarter: all Minors In mul left
-- statement:
--   The Latin Quarter construction uses the all Minors In mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Minors.lean#L29-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Minors.lean#L29-L45

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Ideal.Operations
public import Definitions.Def_LeanPool_LatinQuarter_Minors
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
variable {R : Type*} [CommRing R]

theorem LatinQuarter.allMinorsIn_mul_left {m n p : Type*} [Fintype n]
    (A : Matrix m n R) (B : Matrix n p R) {t : ℕ} {J : Ideal R}
    (hB : AllMinorsIn B t J) : AllMinorsIn (A * B) t J := by sorry
