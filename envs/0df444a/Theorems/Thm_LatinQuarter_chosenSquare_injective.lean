-- Prove2me | Theorems.Thm_LatinQuarter_chosenSquare_injective
-- name    : LatinQuarter.chosenSquare_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:51.567449+00:00
-- url     : https://prove2.me/theorems/75b0495e-d128-4c92-9992-49e352d5f163
-- title:
--   Latin Quarter: chosen Square injective
-- statement:
--   The Latin Quarter construction uses the chosen Square injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Rows.lean#L65-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Rows.lean#L65-L74

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

theorem LatinQuarter.chosenSquare_injective {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (hL : IsLatin L) : Function.Injective (chosenSquare P L) := by sorry
