-- Prove2me | Theorems.Thm_LogLogJam_Supplement_constant_confidence_tomography
-- name    : LogLogJam.Supplement.constant_confidence_tomography
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-26T09:28:43.294942+00:00
-- url     : https://prove2.me/theorems/047174cd-642c-5676-9740-9a70424b39ee
-- title:
--   Theorem 8.16 at failure probability at most one half
-- statement:
--   For $0<\varepsilon\le1/3$ and $0<\delta\le1/2$, every integer $m\ge C\log(1/\delta)/\varepsilon^2$ admits nonadaptive one-copy measurements and a Markov estimator that reconstructs every centered pure single-mode Gaussian state within trace distance $\varepsilon$, with probability at least $1-\delta$. This is the specified confidence range of registered Theorem 8.16.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3.SSS4 — Eqs. (177)–(179).

import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Definitions.Def_BosonicLearn_transcriptLaw
import Definitions.Def_BosonicLearn_traceDist
import Mathlib

open MeasureTheory ProbabilityTheory BosonicLearn
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal

namespace LogLogJam.Supplement

theorem constant_confidence_tomography :
    ∃ C : ℝ, 0 < C ∧ ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 / 3 → 0 < δ → δ ≤ 1 / 2 →
    ∀ m : ℕ, C * Real.log (1 / δ) / ε ^ 2 ≤ m →
    ∃ (S : AdaptiveScheme 1 m ℝ)
      (est : Kernel (Fin m → ℝ) (State (Occupation (Fin 1)))),
      (∀ (t : Fin m) (x y : Fin t → ℝ), S.povm t x = S.povm t y) ∧
      IsMarkovKernel est ∧
      ∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ →
        ENNReal.ofReal (1 - δ) ≤ ∫⁻ x, est x {σ | IsPureCentGauss σ ∧
          traceDist ρ.coefficients σ.coefficients ≤ ENNReal.ofReal ε}
          ∂(transcriptLaw S ρ.coefficients) := by sorry

end LogLogJam.Supplement
