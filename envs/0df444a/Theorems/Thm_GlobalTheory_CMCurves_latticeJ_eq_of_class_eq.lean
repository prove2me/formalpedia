-- Prove2me | Theorems.Thm_GlobalTheory_CMCurves_latticeJ_eq_of_class_eq
-- name    : GlobalTheory.CMCurves.latticeJ_eq_of_class_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:04:46.250883+00:00
-- url     : https://prove2.me/theorems/9f1ba2f0-49cd-40e6-949d-efa14d437765
-- title:
--   CMCurves: lattice J eq of class eq
-- statement:
--   The CMCurves construction uses the lattice J eq of class eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsFieldCmCurvesUnitDiscriminant.lean#L117-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsFieldCmCurvesUnitDiscriminant.lean#L117-L149

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
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.CMCurves.latticeJ_eq_of_class_eq (σ : K →+* ℂ) {L L' : PeriodPair} {𝔞 𝔞' : (Ideal (𝓞 K))⁰}
    {c c' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : ∀ z, z ∈ L.lattice ↔ ∃ a ∈ (𝔞 : Ideal (𝓞 K)), z = c * σ (a : K))
    (h' : ∀ z, z ∈ L'.lattice ↔ ∃ a ∈ (𝔞' : Ideal (𝓞 K)), z = c' * σ (a : K))
    (e : ClassGroup.mk0 𝔞 = ClassGroup.mk0 𝔞') : latticeJ L' = latticeJ L := by sorry
