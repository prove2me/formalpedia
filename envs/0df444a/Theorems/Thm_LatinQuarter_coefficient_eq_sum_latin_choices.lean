-- Prove2me | Theorems.Thm_LatinQuarter_coefficient_eq_sum_latin_choices
-- name    : LatinQuarter.coefficient_eq_sum_latin_choices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:00.476505+00:00
-- url     : https://prove2.me/theorems/13130f4f-625b-42ab-b16c-24b1d3885d67
-- title:
--   Latin Quarter: coefficient eq sum latin choices
-- statement:
--   The highest square-free coefficient counts the Latin row choices modulo two.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Counting.lean#L116-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Counting.lean#L116-L129

module
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
public import Definitions.Def_LeanPool_LatinQuarter_Counting
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial
open Classical

theorem LatinQuarter.coefficient_eq_sum_latin_choices {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (hL : IsLatin L) (a : Cell n → ZMod 2) :
    (clueProduct P L (Matrix.of fun c s => X (c, s) + C (a (c, s))) *
      rowMinorProduct P L (Matrix.of fun c s => X (c, s) + C (a (c, s)))).coeff
      (allTagsExponent (Cell n)) =
      ∑ σ : RowChoices P, if IsLatin (chosenSquare P L σ) then (1 : ZMod 2) else 0 := by sorry
