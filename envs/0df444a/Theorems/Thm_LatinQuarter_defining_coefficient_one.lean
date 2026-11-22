-- Prove2me | Theorems.Thm_LatinQuarter_defining_coefficient_one
-- name    : LatinQuarter.defining_coefficient_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:11.508121+00:00
-- url     : https://prove2.me/theorems/ef85a0b2-9af8-44c9-b7d7-71738e3c2276
-- title:
--   Latin Quarter: defining coefficient one
-- statement:
--   Adding constants preserves the completion coefficient, and unique
--   completion makes that coefficient exactly one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Counting.lean#L133-L145
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Counting.lean#L133-L145

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

theorem LatinQuarter.defining_coefficient_one {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (h : IsDefining P L) (a : Cell n → ZMod 2) :
    (clueProduct P L (Matrix.of fun c s => X (c, s) + C (a (c, s))) *
      rowMinorProduct P L (Matrix.of fun c s => X (c, s) + C (a (c, s)))).coeff
      (allTagsExponent (Cell n)) = 1 := by sorry
