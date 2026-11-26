-- Prove2me | Theorems.Thm_LogLogJam_Supplement_one_readout_localization
-- name    : LogLogJam.Supplement.one_readout_localization
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T19:26:43.897553+00:00
-- url     : https://prove2.me/theorems/da041fc7-047a-568b-8de7-d081ca9236cc
-- title:
--   One-observation small-ball localization for centered pure one-mode Gaussian states
-- statement:
--   For every positive number of copies there is a nonadaptive single-copy scheme and a Markov estimator whose chance of returning a centered pure Gaussian state within trace error ε is at least a universal multiple of ε², uniformly in the input state. The lower bound is independent of the copy count; a single informative readout suffices.
-- source:
--   https://arxiv.org/abs/2607.12983, Theorem 8.16. Fixed-budget refinement for the full confidence range.

import Mathlib
import Definitions.Def_LogLogJam_Supplement_IsGaussQP
import Definitions.Def_BosonicLearn_transcriptLaw
import Definitions.Def_BosonicLearn_traceDist

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace LogLogJam.Supplement

theorem one_readout_localization :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 3 →
    ∀ m : ℕ, 1 ≤ m →
      ∃ (S : BosonicLearn.AdaptiveScheme 1 m ℝ)
        (est : Kernel (Fin m → ℝ) (State (Occupation (Fin 1)))),
        (∀ (t : Fin m) (x x' : Fin t → ℝ), S.povm t x = S.povm t x') ∧
        IsMarkovKernel est ∧
        ∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ →
          ENNReal.ofReal (c * ε^2) ≤
            ∫⁻ x, est x {σ | IsPureCentGauss σ ∧
                BosonicLearn.traceDist ρ.coefficients σ.coefficients ≤ ENNReal.ofReal ε}
              ∂(BosonicLearn.transcriptLaw S ρ.coefficients) := by sorry

end LogLogJam.Supplement
