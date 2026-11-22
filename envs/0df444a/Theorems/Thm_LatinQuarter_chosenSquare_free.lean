-- Prove2me | Theorems.Thm_LatinQuarter_chosenSquare_free
-- name    : LatinQuarter.chosenSquare_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:40.333552+00:00
-- url     : https://prove2.me/theorems/dc2e08ce-90d2-44ed-b6c4-239d5d5a8a09
-- title:
--   Latin Quarter: chosen Square free
-- statement:
--   The Latin Quarter construction uses the chosen Square free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Rows.lean#L35-L39
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Rows.lean#L35-L39

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

theorem LatinQuarter.chosenSquare_free {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (σ : RowChoices P) (r : Fin n) (c : FreeColumn P r) :
    chosenSquare P L σ r c = L r (σ r c) := by sorry
