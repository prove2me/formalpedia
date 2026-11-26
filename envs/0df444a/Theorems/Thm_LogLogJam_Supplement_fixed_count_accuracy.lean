-- Prove2me | Theorems.Thm_LogLogJam_Supplement_fixed_count_accuracy
-- name    : LogLogJam.Supplement.fixed_count_accuracy
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-26T09:27:18.265113+00:00
-- url     : https://prove2.me/theorems/fae38a9d-f34c-5f7a-8320-c75d6b2363c2
-- title:
--   Estimating the photon-number mean on the fixed count readout
-- statement:
--   For any prescribed phase-and-count scheme and sufficient budget $m\ge C\log(2/\delta)/\eta^2$, a measurable nonnegative estimator using only the photon-number outcomes recovers $\sinh^2 r$ to additive accuracy $\eta\sinh(r)\cosh(r)$ except with probability $\delta$. This is the mean-estimation step before conversion to squeezing error.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3 — Lemma 8.27 and Eqs. (171)–(173).

import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Definitions.Def_BosonicLearn_transcriptLaw
import Mathlib
import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Definitions.Def_BosonicLearn_transcriptLaw

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace LogLogJam.Supplement

theorem fixed_count_accuracy :
    ∃ C > (0 : ℝ), ∀ η δ : ℝ, 0 < η → η ≤ 1 / 4 → 0 < δ → δ < 1 →
    ∀ m : ℕ, C * Real.log (2 / δ) / η^2 ≤ m →
    ∀ S : BosonicLearn.AdaptiveScheme 1 m ℝ, phaseCountReadouts S →
    ∃ mean : (Fin m → ℝ) → ℝ, Measurable mean ∧ (∀ x, 0 ≤ mean x) ∧
      (∀ x y, (∀ i : Fin m, m / 2 ≤ i.val → x i = y i) → mean x = mean y) ∧
      ∀ (ρ : State (Occupation (Fin 1))) (r θ : ℝ), squeezedAt ρ r θ →
        BosonicLearn.transcriptLaw S ρ.coefficients
          {x | η * Real.cosh r * Real.sinh r < |mean x - Real.sinh r ^ 2|} ≤ ENNReal.ofReal δ := by sorry

end LogLogJam.Supplement
