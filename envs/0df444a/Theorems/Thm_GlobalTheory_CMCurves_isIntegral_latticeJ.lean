-- Prove2me | Theorems.Thm_GlobalTheory_CMCurves_isIntegral_latticeJ
-- name    : GlobalTheory.CMCurves.isIntegral_latticeJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:52.924405+00:00
-- url     : https://prove2.me/theorems/b542824f-f3b1-4bdf-bf52-2d239ddc1f68
-- title:
--   CMCurves: is Integral lattice J
-- statement:
--   The CMCurves construction uses the is Integral lattice J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsFieldCmCurvesUnitDiscriminant.lean#L100-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsFieldCmCurvesUnitDiscriminant.lean#L100-L115

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

theorem GlobalTheory.CMCurves.isIntegral_latticeJ (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (L : PeriodPair)
    (hL : ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice) :
    IsIntegral ℤ (latticeJ L) := by sorry
