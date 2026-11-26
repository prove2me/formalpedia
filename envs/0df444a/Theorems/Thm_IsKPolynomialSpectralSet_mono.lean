-- Prove2me | Theorems.Thm_IsKPolynomialSpectralSet_mono
-- name    : IsKPolynomialSpectralSet.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:07:21.366103+00:00
-- url     : https://prove2.me/theorems/8bfd3925-0a77-4a5f-bfd4-4d64289ef243
-- title:
--   Is KPolynomial Spectral Set: mono
-- statement:
--   Simultaneously enlarge the constant and a compact control set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetMonotone.lean#L37-L42
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetMonotone.lean#L37-L42

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
set_option autoImplicit false
open Set
open scoped InnerProductSpace Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem IsKPolynomialSpectralSet.mono
    {A : E →L[ℂ] E} {K L : ℝ} {X Y : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X) (hK : 0 ≤ K)
    (hKL : K ≤ L) (hXY : X ⊆ Y) (hY : IsCompact Y) :
    IsKPolynomialSpectralSet A L Y := by sorry
