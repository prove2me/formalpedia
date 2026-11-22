-- Prove2me | Theorems.Thm_LatinQuarter_columnSymbol_bijective
-- name    : LatinQuarter.columnSymbol_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:14.600644+00:00
-- url     : https://prove2.me/theorems/38884aad-1ec2-44e5-8076-e0a9529182fd
-- title:
--   Latin Quarter: column Symbol bijective
-- statement:
--   The Latin Quarter construction uses the column Symbol bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Counting.lean#L67-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Counting.lean#L67-L76

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

theorem LatinQuarter.columnSymbol_bijective {n : ℕ} {M : Square n} (hM : IsLatin M) :
    Function.Bijective (columnSymbol M) := by sorry
