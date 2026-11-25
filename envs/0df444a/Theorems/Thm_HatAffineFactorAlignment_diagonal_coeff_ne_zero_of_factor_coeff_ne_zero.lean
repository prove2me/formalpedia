-- Prove2me | Theorems.Thm_HatAffineFactorAlignment_diagonal_coeff_ne_zero_of_factor_coeff_ne_zero
-- name    : HatAffineFactorAlignment.diagonal_coeff_ne_zero_of_factor_coeff_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:10:40.273519+00:00
-- url     : https://prove2.me/theorems/8b6c80db-7d3a-4e2d-8973-2b1cf2da60de
-- title:
--   Hat Affine Factor Alignment: diagonal coeff ne zero of factor coeff ne zero
-- statement:
--   The Hat Affine Factor Alignment construction uses the diagonal coeff ne zero of factor coeff ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFactorAlignment/FactorShape.lean#L99-L125
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFactorAlignment/FactorShape.lean#L99-L125

import Definitions.Def_HatAffineGenericCore_G3A
import Definitions.Def_HatAffineFactorAlignment_FactorShape
set_option autoImplicit true
open scoped BigOperators
open HatAffineFactorAlignment
universe u
open Finset
open MvPolynomial
open HatAffineGenericCore

theorem HatAffineFactorAlignment.diagonal_coeff_ne_zero_of_factor_coeff_ne_zero
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hq : 3 ≤ Fintype.card K)
    (a lambda : Fin m → K)
    (hlambda : lambda ≠ 0)
    (hdiv : linearForm a ∣ diagonalForm lambda)
    (r : Fin m) (har : a r ≠ 0) :
    lambda r ≠ 0 := by sorry
