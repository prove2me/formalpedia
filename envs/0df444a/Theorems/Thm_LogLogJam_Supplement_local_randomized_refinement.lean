-- Prove2me | Theorems.Thm_LogLogJam_Supplement_local_randomized_refinement
-- name    : LogLogJam.Supplement.local_randomized_refinement
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T19:27:02.512955+00:00
-- url     : https://prove2.me/theorems/b8f9337b-07b5-4070-9eb5-460e99bcb1f8
-- title:
--   Local random refinement on the two-dimensional squeezed-state family
-- statement:
--   Given a centered pure one-mode Gaussian estimate within trace distance d≤1/3 of the true pure centered Gaussian, there is a state-independent Markov rule to refine it. For 0<ε≤d the refined estimate is pure and ε-accurate with probability at least a universal constant times (ε/d)².
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

theorem local_randomized_refinement :
    ∃ a > (0 : ℝ), ∀ ε d : ℝ, 0 < ε → ε ≤ d → d ≤ 1 / 3 →
      ∃ L : Kernel (State (Occupation (Fin 1))) (State (Occupation (Fin 1))),
        IsMarkovKernel L ∧ ∀ σ ρ : State (Occupation (Fin 1)), IsPureCentGauss σ → IsPureCentGauss ρ →
          BosonicLearn.traceDist ρ.coefficients σ.coefficients ≤ ENNReal.ofReal d →
          ENNReal.ofReal (a * (ε/d)^2) ≤ L σ {τ | IsPureCentGauss τ ∧
            BosonicLearn.traceDist ρ.coefficients τ.coefficients ≤ ENNReal.ofReal ε} := by sorry

end LogLogJam.Supplement
