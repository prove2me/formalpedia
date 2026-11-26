-- Prove2me | Theorems.Thm_IsPolynomialSpectralSet_affine
-- name    : IsPolynomialSpectralSet.affine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:39:23.054987+00:00
-- url     : https://prove2.me/theorems/66f0155a-96f4-4a85-b3e4-b034ebbabed2
-- title:
--   Is Polynomial Spectral Set: affine
-- statement:
--   Invertible affine changes preserve the constant-one polynomial
--   spectral-set property.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineSpectralSet.lean#L95-L101
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineSpectralSet.lean#L95-L101

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AffineSpectralSet
set_option autoImplicit false
open Set
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem IsPolynomialSpectralSet.affine
    {A : E →L[ℂ] E} {X : Set ℂ}
    (h : IsPolynomialSpectralSet A X)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsPolynomialSpectralSet (a • A + b • 1)
      ((fun z => a * z + b) '' X) := by sorry
