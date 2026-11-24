-- Prove2me | Theorems.Thm_GlobalTheory_exists_field_cm_curves_unit_discriminant
-- name    : GlobalTheory.exists_field_cm_curves_unit_discriminant
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:25.098204+00:00
-- url     : https://prove2.me/theorems/9b967d54-0d87-4583-8e19-3e8af430247e
-- title:
--   Global Theory: exists field cm curves unit discriminant
-- statement:
--   The Global Theory construction uses the exists field cm curves unit discriminant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsFieldCmCurvesUnitDiscriminant.lean#L173-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsFieldCmCurvesUnitDiscriminant.lean#L173-L239

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
open CMCurves

theorem GlobalTheory.exists_field_cm_curves_unit_discriminant :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ : K →+* ℂ),
    ¬ NumberField.ComplexEmbedding.IsReal σ →
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ a, σ a ∈ M) ∧
      ∀ L : PeriodPair, (∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice) →
        ∃ W : WeierstrassCurve (𝓞 M), IsUnit W.Δ ∧
          (((W.c₄ : M) : ℂ)) ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) =
            1728 * L.g₂ ^ 3 * ((W.Δ : M) : ℂ) := by sorry
