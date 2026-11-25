-- Prove2me | Theorems.Thm_HatAffineFactorAlignment_diagonal_coeff_eq_zero_of_factor_coeff_eq_zero
-- name    : HatAffineFactorAlignment.diagonal_coeff_eq_zero_of_factor_coeff_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:10:20.920844+00:00
-- url     : https://prove2.me/theorems/cef69970-6d90-58cb-a189-96c8153bfe32
-- title:
--   Hat Affine Factor Alignment: diagonal coeff eq zero of factor coeff eq zero
-- statement:
--   The Hat Affine Factor Alignment construction uses the diagonal coeff eq zero of factor coeff eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFactorAlignment/FactorShape.lean#L82-L97
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFactorAlignment/FactorShape.lean#L82-L97

import Definitions.Def_HatAffineGenericCore_G3A
import Definitions.Def_HatAffineFactorAlignment_FactorShape
set_option autoImplicit true
open scoped BigOperators
open HatAffineFactorAlignment
universe u
open Finset
open MvPolynomial
open HatAffineGenericCore

theorem HatAffineFactorAlignment.diagonal_coeff_eq_zero_of_factor_coeff_eq_zero
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hq : 3 ≤ Fintype.card K)
    (a lambda : Fin m → K)
    (hdiv : linearForm a ∣ diagonalForm lambda)
    (r : Fin m) (har : a r = 0) :
    lambda r = 0 := by sorry
