-- Prove2me | Theorems.Thm_IsKPolynomialSpectralSet_mono_const
-- name    : IsKPolynomialSpectralSet.mono_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:16.679314+00:00
-- url     : https://prove2.me/theorems/8a8f1d20-0596-4383-847f-3142557cd215
-- title:
--   Is KPolynomial Spectral Set: mono const
-- statement:
--   A polynomial spectral-set estimate remains true with a larger constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetMonotone.lean#L16-L21
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetMonotone.lean#L16-L21

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
set_option autoImplicit false
open Set
open scoped InnerProductSpace Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem IsKPolynomialSpectralSet.mono_const
    {A : E →L[ℂ] E} {K L : ℝ} {X : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X) (hKL : K ≤ L) :
    IsKPolynomialSpectralSet A L X := by sorry
