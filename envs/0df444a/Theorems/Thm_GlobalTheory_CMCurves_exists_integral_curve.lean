-- Prove2me | Theorems.Thm_GlobalTheory_CMCurves_exists_integral_curve
-- name    : GlobalTheory.CMCurves.exists_integral_curve
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:04:05.524908+00:00
-- url     : https://prove2.me/theorems/2f204b46-20a2-4324-abae-3b4239928383
-- title:
--   CMCurves: exists integral curve
-- statement:
--   The CMCurves construction uses the exists integral curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsFieldCmCurvesUnitDiscriminant.lean#L21-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsFieldCmCurvesUnitDiscriminant.lean#L21-L55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsFieldCmCurvesUnitDiscriminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField
open scoped nonZeroDivisors UpperHalfPlane
noncomputable section
open GlobalTheory
open GlobalTheory.CMCurves

theorem GlobalTheory.CMCurves.exists_integral_curve {j : ℂ} (hj : IsIntegral ℤ j) :
    ∃ E : WeierstrassCurve ℂ, IsIntegral ℤ E.a₁ ∧ IsIntegral ℤ E.a₂ ∧ IsIntegral ℤ E.a₃ ∧
      IsIntegral ℤ E.a₄ ∧ IsIntegral ℤ E.a₆ ∧ E.Δ = 1 ∧ E.c₄ ^ 3 = j := by sorry
