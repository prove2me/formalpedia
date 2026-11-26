-- Prove2me | Theorems.Thm_IsPolynomialSpectralSet_mono_set
-- name    : IsPolynomialSpectralSet.mono_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:21:56.59624+00:00
-- url     : https://prove2.me/theorems/76a5f787-2a38-4274-94c5-3368b9a0c62d
-- title:
--   Is Polynomial Spectral Set: mono set
-- statement:
--   A constant-one polynomial spectral set remains one after compact
--   enlargement.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetMonotone.lean#L46-L51
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetMonotone.lean#L46-L51

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
set_option autoImplicit false
open Set
open scoped InnerProductSpace Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem IsPolynomialSpectralSet.mono_set
    {A : E →L[ℂ] E} {X Y : Set ℂ}
    (h : IsPolynomialSpectralSet A X)
    (hXY : X ⊆ Y) (hY : IsCompact Y) :
    IsPolynomialSpectralSet A Y := by sorry
