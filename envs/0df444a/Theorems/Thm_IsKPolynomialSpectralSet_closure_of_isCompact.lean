-- Prove2me | Theorems.Thm_IsKPolynomialSpectralSet_closure_of_isCompact
-- name    : IsKPolynomialSpectralSet.closure_of_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:07:36.229395+00:00
-- url     : https://prove2.me/theorems/b393968e-c403-4284-93f0-c3e41771f261
-- title:
--   Is KPolynomial Spectral Set: closure of is Compact
-- statement:
--   Compact control sets can be closed without changing a polynomial
--   spectral-set estimate.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetMonotone.lean#L68-L72
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetMonotone.lean#L68-L72

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
set_option autoImplicit false
open Set
open scoped InnerProductSpace Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem IsKPolynomialSpectralSet.closure_of_isCompact
    {A : E →L[ℂ] E} {K : ℝ} {X : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X) (hX : IsCompact X) :
    IsKPolynomialSpectralSet A K (closure X) := by sorry
