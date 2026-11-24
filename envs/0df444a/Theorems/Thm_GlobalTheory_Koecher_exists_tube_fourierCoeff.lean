-- Prove2me | Theorems.Thm_GlobalTheory_Koecher_exists_tube_fourierCoeff
-- name    : GlobalTheory.Koecher.exists_tube_fourierCoeff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:49:43.370876+00:00
-- url     : https://prove2.me/theorems/59cdf8e4-8a2d-4462-ba5b-e0fb6ca543aa
-- title:
--   Koecher: exists tube fourier Coeff
-- statement:
--   The Koecher construction uses the exists tube fourier Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/NormLeTsumOfCubeFourierCoeffLe.lean#L113-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/NormLeTsumOfCubeFourierCoeffLe.lean#L113-L184

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.Koecher

theorem GlobalTheory.Koecher.exists_tube_fourierCoeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℂ) → ℂ} {U : Set (ι → ℂ)} (hU : IsOpen U) (hU' : IsPreconnected U)
    (htube : ∀ z ∈ U, ∀ t : ι → ℝ, (fun i => (t i : ℂ)) + z ∈ U) (hf : DifferentiableOn ℂ f U)
    (hper : ∀ z ∈ U, ∀ i, f (z + Pi.single i 1) = f z) :
    ∃ a : (ι → ℤ) → ℝ, (∀ m, 0 ≤ a m) ∧
      (∀ z ∈ U, ∀ M : ℝ, (∀ t : ι → ℝ, ‖f ((fun i => (t i : ℂ)) + z)‖ ≤ M) →
        ∀ m, a m * Real.exp (-(2 * π * ∑ i, (m i : ℝ) * (z i).im)) ≤ M) ∧
      (∀ z ∈ U, ∀ b : (ι → ℤ) → ℝ, Summable b →
        (∀ m, a m * Real.exp (-(2 * π * ∑ i, (m i : ℝ) * (z i).im)) ≤ b m) →
          ‖f z‖ ≤ ∑' m, b m) := by sorry
