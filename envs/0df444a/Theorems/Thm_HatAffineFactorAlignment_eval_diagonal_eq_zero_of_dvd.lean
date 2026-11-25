-- Prove2me | Theorems.Thm_HatAffineFactorAlignment_eval_diagonal_eq_zero_of_dvd
-- name    : HatAffineFactorAlignment.eval_diagonal_eq_zero_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:07:31.884801+00:00
-- url     : https://prove2.me/theorems/f1cdba68-033e-4ab5-84ab-b4cbc36870e0
-- title:
--   Hat Affine Factor Alignment: eval diagonal eq zero of dvd
-- statement:
--   The Hat Affine Factor Alignment construction uses the eval diagonal eq zero of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFactorAlignment/FactorShape.lean#L72-L80
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFactorAlignment/FactorShape.lean#L72-L80

import Definitions.Def_HatAffineGenericCore_G3A
import Definitions.Def_HatAffineFactorAlignment_FactorShape
set_option autoImplicit true
open scoped BigOperators
open HatAffineFactorAlignment
universe u
open Finset
open MvPolynomial
open HatAffineGenericCore

theorem HatAffineFactorAlignment.eval_diagonal_eq_zero_of_dvd
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    {a lambda : Fin m → K}
    (hdiv : linearForm a ∣ diagonalForm lambda)
    {y : Fin m → K}
    (hy : MvPolynomial.eval y (linearForm a) = 0) :
    MvPolynomial.eval y (diagonalForm lambda) = 0 := by sorry
