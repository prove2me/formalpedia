-- Prove2me | Theorems.Thm_LogLogJam_Supplement_weak_success_localization
-- name    : LogLogJam.Supplement.weak_success_localization
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:27:37.130558+00:00
-- url     : https://prove2.me/theorems/c5fd8258-9f9e-5613-8fe6-ba67ada19a15
-- title:
--   Weak-success localization with a fixed budget of single-copy measurements
-- statement:
--   For each $m\ge1$ and $0<\varepsilon\le1/3$, there is a nonadaptive, single-copy scheme and a randomized estimator for centered pure one-mode Gaussian states whose probability of returning a centered pure estimate within trace distance $\varepsilon$ is at least $\min\{1/2,c m\varepsilon^2\}$ uniformly in the input and its energy, for an absolute $c>0$. This expresses the small-success content of the registered all-confidence target in fixed-budget form. It includes $m=1$. Its proof at small budgets is open.
-- source:
--   Auxiliary fixed-budget formulation of the weak-success regime of the registered Theorem 8.16, Chen, Gong, Ye and Zhang, §8.3, arXiv:2607.12983v1. https://arxiv.org/html/2607.12983v1#S8.SS3

import Mathlib
import Definitions.Def_LogLogJam_Supplement_IsGaussQP
import Definitions.Def_BosonicLearn_transcriptLaw
import Definitions.Def_BosonicLearn_traceDist

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace LogLogJam.Supplement

theorem weak_success_localization :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 3 →
    ∀ m : ℕ, 1 ≤ m →
      ∃ (S : BosonicLearn.AdaptiveScheme 1 m ℝ)
        (est : Kernel (Fin m → ℝ) (State (Occupation (Fin 1)))),
        (∀ (t : Fin m) (x x' : Fin t → ℝ), S.povm t x = S.povm t x') ∧
        IsMarkovKernel est ∧
        ∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ →
          ENNReal.ofReal (min (1/2) (c * (m : ℝ) * ε^2)) ≤
            ∫⁻ x, est x {σ | IsPureCentGauss σ ∧
                BosonicLearn.traceDist ρ.coefficients σ.coefficients ≤ ENNReal.ofReal ε}
              ∂(BosonicLearn.transcriptLaw S ρ.coefficients) := by sorry

end LogLogJam.Supplement
