-- Prove2me | Theorems.Thm_LatinQuarter_coefficient_eq_card_latin_choices
-- name    : LatinQuarter.coefficient_eq_card_latin_choices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:22:12.396029+00:00
-- url     : https://prove2.me/theorems/c8b3e878-999b-41e5-98a4-548224384e4e
-- title:
--   Latin Quarter: coefficient eq card latin choices
-- statement:
--   The square-free coefficient counts the Latin row choices modulo two.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Parity.lean#L32-L39
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Parity.lean#L32-L39

module
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_Parity
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial
open Classical

theorem LatinQuarter.coefficient_eq_card_latin_choices {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (hL : IsLatin L) (a : Cell n → ZMod 2) :
    (clueProduct P L (Matrix.of fun c s => X (c, s) + C (a (c, s))) *
      rowMinorProduct P L (Matrix.of fun c s => X (c, s) + C (a (c, s)))).coeff
      (allTagsExponent (Cell n)) =
      ((Finset.univ.filter
        (fun σ : RowChoices P => IsLatin (chosenSquare P L σ))).card : ZMod 2) := by sorry
