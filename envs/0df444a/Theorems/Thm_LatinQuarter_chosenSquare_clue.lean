-- Prove2me | Theorems.Thm_LatinQuarter_chosenSquare_clue
-- name    : LatinQuarter.chosenSquare_clue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:46.579597+00:00
-- url     : https://prove2.me/theorems/aa28f135-675b-4960-8aca-9c5f33a20493
-- title:
--   Latin Quarter: chosen Square clue
-- statement:
--   The Latin Quarter construction uses the chosen Square clue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Rows.lean#L41-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Rows.lean#L41-L45

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

theorem LatinQuarter.chosenSquare_clue {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (σ : RowChoices P) (r c : Fin n) (hc : (r, c) ∈ P) :
    chosenSquare P L σ r c = L r c := by sorry
