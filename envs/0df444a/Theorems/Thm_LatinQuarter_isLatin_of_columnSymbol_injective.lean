-- Prove2me | Theorems.Thm_LatinQuarter_isLatin_of_columnSymbol_injective
-- name    : LatinQuarter.isLatin_of_columnSymbol_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:13.007503+00:00
-- url     : https://prove2.me/theorems/c42f7787-737b-417b-aa1c-e4228419acab
-- title:
--   Latin Quarter: is Latin of column Symbol injective
-- statement:
--   The Latin Quarter construction uses the is Latin of column Symbol injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Counting.lean#L78-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Counting.lean#L78-L84

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

theorem LatinQuarter.isLatin_of_columnSymbol_injective {n : ℕ} {M : Square n}
    (hr : ∀ r, Function.Bijective (M r)) (hi : Function.Injective (columnSymbol M)) :
    IsLatin M := by sorry
