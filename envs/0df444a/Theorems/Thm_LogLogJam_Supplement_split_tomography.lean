-- Prove2me | Theorems.Thm_LogLogJam_Supplement_split_tomography
-- name    : LogLogJam.Supplement.split_tomography
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:28:08.635854+00:00
-- url     : https://prove2.me/theorems/c051cf16-473c-57fa-a13c-87370a2727f6
-- title:
--   Tomography with a fixed phase-and-count measurement schedule
-- statement:
--   With the fixed phase-and-count schedule, a single measurable estimator returns a centered pure one-mode Gaussian state for every transcript. For $0<\eta\le 1/4$, $0<\delta<1$ and $m\ge C\log(2/\delta)/\eta^2$, its trace error exceeds $5\eta$ with probability at most $2\delta$ for every such input state. The constant is independent of squeezing.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3 — §8.3.4, proof of Theorem 8.16.

import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Definitions.Def_BosonicLearn_transcriptLaw
import Definitions.Def_BosonicLearn_traceDist
import Mathlib

open MeasureTheory BosonicLearn
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal

namespace LogLogJam.Supplement

theorem split_tomography :
    ∃ C > (0 : ℝ), ∀ η δ : ℝ, 0 < η → η ≤ 1 / 4 → 0 < δ → δ < 1 →
    ∀ m : ℕ, C * Real.log (2 / δ) / η^2 ≤ m →
    ∃ (S : AdaptiveScheme 1 m ℝ) (est : (Fin m → ℝ) → State (Occupation (Fin 1))),
      phaseCountReadouts S ∧ Measurable est ∧ (∀ x, IsPureCentGauss (est x)) ∧
      ∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ →
        transcriptLaw S ρ.coefficients
          {x | ENNReal.ofReal (5 * η) < traceDist ρ.coefficients (est x).coefficients} ≤
            ENNReal.ofReal (2 * δ) := by sorry

end LogLogJam.Supplement
