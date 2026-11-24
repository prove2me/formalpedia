-- Prove2me | Theorems.Thm_GlobalTheory_CMCurves_finite_latticeJ
-- name    : GlobalTheory.CMCurves.finite_latticeJ
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:03:40.272116+00:00
-- url     : https://prove2.me/theorems/13234889-93cd-4a3b-8845-0193aaf11bc9
-- title:
--   CMCurves: finite lattice J
-- statement:
--   The CMCurves construction uses the finite lattice J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsFieldCmCurvesUnitDiscriminant.lean#L151-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsFieldCmCurvesUnitDiscriminant.lean#L151-L167

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

theorem GlobalTheory.CMCurves.finite_latticeJ (σ : K →+* ℂ) (hσ : ¬ ComplexEmbedding.IsReal σ) :
    (latticeJ '' {L | ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice}).Finite := by sorry
