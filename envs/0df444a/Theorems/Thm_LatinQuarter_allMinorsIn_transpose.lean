-- Prove2me | Theorems.Thm_LatinQuarter_allMinorsIn_transpose
-- name    : LatinQuarter.allMinorsIn_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:33.263719+00:00
-- url     : https://prove2.me/theorems/acea7b99-0584-4bd6-9188-e16bb8fc3a8b
-- title:
--   Latin Quarter: all Minors In transpose
-- statement:
--   The Latin Quarter construction uses the all Minors In transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Minors.lean#L47-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Minors.lean#L47-L51

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

theorem LatinQuarter.allMinorsIn_transpose {m n : Type*} (M : Matrix m n R)
    {t : ℕ} {J : Ideal R} (hM : AllMinorsIn M t J) :
    AllMinorsIn M.transpose t J := by sorry
