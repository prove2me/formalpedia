-- Prove2me | Theorems.Thm_IsKPolynomialSpectralSet_closure_of_isBounded
-- name    : IsKPolynomialSpectralSet.closure_of_isBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:21.434498+00:00
-- url     : https://prove2.me/theorems/9758312a-5b54-5878-9771-21e3df8687bd
-- title:
--   Is KPolynomial Spectral Set: closure of is Bounded
-- statement:
--   Passing from a bounded control set to its closure preserves the spectral
--   set constant exactly.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetMonotone.lean#L55-L64
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetMonotone.lean#L55-L64

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
set_option autoImplicit false
open Set
open scoped InnerProductSpace Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem IsKPolynomialSpectralSet.closure_of_isBounded
    {A : E →L[ℂ] E} {K : ℝ} {X : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X)
    (hX : Bornology.IsBounded X) :
    IsKPolynomialSpectralSet A K (closure X) := by sorry
