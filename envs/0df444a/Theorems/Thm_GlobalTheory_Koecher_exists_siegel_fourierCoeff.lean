-- Prove2me | Theorems.Thm_GlobalTheory_Koecher_exists_siegel_fourierCoeff
-- name    : GlobalTheory.Koecher.exists_siegel_fourierCoeff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:49:09.817535+00:00
-- url     : https://prove2.me/theorems/c6abcf6f-0d2d-4670-b045-9b4965d92302
-- title:
--   Koecher: exists siegel fourier Coeff
-- statement:
--   The Koecher construction uses the exists siegel fourier Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/NormLeTsumOfCubeFourierCoeffLe.lean#L201-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/NormLeTsumOfCubeFourierCoeffLe.lean#L201-L299

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
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key

theorem GlobalTheory.Koecher.exists_siegel_fourierCoeff {g N : ℕ} (hN : 1 ≤ N) {F : Matrix (Fin g) (Fin g) ℂ → ℂ}
    (hF : IsHoloSiegel g F)
    (hper : ∀ B : Matrix (Fin g) (Fin g) ℤ, B.IsSymm → ∀ τ ∈ SiegelH (Fin g),
        F (τ + (N : ℂ) • B.map (Int.cast : ℤ → ℂ)) = F τ) :
    (∀ Y : Matrix (Fin g) (Fin g) ℝ, Y.PosDef → ∃ M : ℝ, ∀ τ : Matrix (Fin g) (Fin g) ℂ,
      τ.IsSymm → τ.map Complex.im = Y → ‖F τ‖ ≤ M) ∧
    ∃ a : (Fin g × Fin g → ℤ) → ℝ, (∀ m, 0 ≤ a m) ∧
      (∀ Y : Matrix (Fin g) (Fin g) ℝ, ((N : ℝ) • (Y + Yᵀ)).PosDef → ∀ M : ℝ,
        (∀ τ : Matrix (Fin g) (Fin g) ℂ, τ.IsSymm → τ.map Complex.im = (N : ℝ) • (Y + Yᵀ) →
          ‖F τ‖ ≤ M) →
        ∀ m, a m * Real.exp (-(2 * π * ∑ q, (m q : ℝ) * Y q.1 q.2)) ≤ M) ∧
      (∀ τ ∈ SiegelH (Fin g), ∀ b : (Fin g × Fin g → ℤ) → ℝ, Summable b →
        (∀ m, a m * Real.exp (-(π / N * ∑ q, (m q : ℝ) * (τ q.1 q.2).im)) ≤ b m) →
          ‖F τ‖ ≤ ∑' m, b m) := by sorry
