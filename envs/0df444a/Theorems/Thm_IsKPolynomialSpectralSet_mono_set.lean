-- Prove2me | Theorems.Thm_IsKPolynomialSpectralSet_mono_set
-- name    : IsKPolynomialSpectralSet.mono_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:41.586873+00:00
-- url     : https://prove2.me/theorems/97903ed5-eff1-40f1-804b-4ff8a857f870
-- title:
--   Is KPolynomial Spectral Set: mono set
-- statement:
--   With a nonnegative constant, enlarging a compact control set preserves a
--   polynomial spectral-set estimate.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetMonotone.lean#L25-L34
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetMonotone.lean#L25-L34

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
set_option autoImplicit false
open Set
open scoped InnerProductSpace Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem IsKPolynomialSpectralSet.mono_set
    {A : E →L[ℂ] E} {K : ℝ} {X Y : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X) (hK : 0 ≤ K)
    (hXY : X ⊆ Y) (hY : IsCompact Y) :
    IsKPolynomialSpectralSet A K Y := by sorry
