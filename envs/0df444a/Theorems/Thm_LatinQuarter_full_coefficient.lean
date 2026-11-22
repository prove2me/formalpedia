-- Prove2me | Theorems.Thm_LatinQuarter_full_coefficient
-- name    : LatinQuarter.full_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:12.037268+00:00
-- url     : https://prove2.me/theorems/05e7cf51-a10b-4d45-8cbc-e73cf194d1c0
-- title:
--   Latin Quarter: full coefficient
-- statement:
--   The full square-free coefficient is one for a Latin square and zero
--   for a row permutation that repeats a symbol in a column.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Counting.lean#L89-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Counting.lean#L89-L112

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

theorem LatinQuarter.full_coefficient {n : ℕ} (M : Square n)
    (hr : ∀ r, Function.Bijective (M r)) :
    (∏ p : Cell n, X (columnSymbol M p) : MvPolynomial (Cell n) (ZMod 2)).coeff
      (allTagsExponent (Cell n)) =
      if IsLatin M then 1 else 0 := by sorry
