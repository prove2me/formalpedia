-- Prove2me | Theorems.Thm_LatinQuarter_allMinorsIn_mul_right
-- name    : LatinQuarter.allMinorsIn_mul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:34.657169+00:00
-- url     : https://prove2.me/theorems/f0657986-be51-4038-acec-f3c207a5ed4a
-- title:
--   Latin Quarter: all Minors In mul right
-- statement:
--   The Latin Quarter construction uses the all Minors In mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Minors.lean#L53-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Minors.lean#L53-L58

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

theorem LatinQuarter.allMinorsIn_mul_right {m n p : Type*} [Fintype n]
    (A : Matrix m n R) (B : Matrix n p R) {t : ℕ} {J : Ideal R}
    (hA : AllMinorsIn A t J) : AllMinorsIn (A * B) t J := by sorry
