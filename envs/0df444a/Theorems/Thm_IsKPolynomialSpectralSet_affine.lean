-- Prove2me | Theorems.Thm_IsKPolynomialSpectralSet_affine
-- name    : IsKPolynomialSpectralSet.affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:01:18.955396+00:00
-- url     : https://prove2.me/theorems/ff96f3ab-bf10-5ab0-9edc-42db2af8ba5d
-- title:
--   Is KPolynomial Spectral Set: affine
-- statement:
--   A polynomial spectral-set estimate is transported by an invertible
--   affine change of variables, with the same constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineSpectralSet.lean#L41-L60
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineSpectralSet.lean#L41-L60

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AffineSpectralSet
set_option autoImplicit false
open Set
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem IsKPolynomialSpectralSet.affine
    {A : E →L[ℂ] E} {K : ℝ} {X : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsKPolynomialSpectralSet (a • A + b • 1) K
      ((fun z => a * z + b) '' X) := by sorry
