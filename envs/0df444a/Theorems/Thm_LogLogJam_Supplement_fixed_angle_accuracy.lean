-- Prove2me | Theorems.Thm_LogLogJam_Supplement_fixed_angle_accuracy
-- name    : LogLogJam.Supplement.fixed_angle_accuracy
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:25:11.984518+00:00
-- url     : https://prove2.me/theorems/290a264b-a0d5-4346-8756-78d24d4033e2
-- title:
--   Estimating the squeezing axis from the fixed phase readout
-- statement:
--   For any prescribed scheme realizing the phase-and-count readouts, a measurable angle estimator depending only on its phase outcomes estimates the squeezing axis within equal-squeezing trace-distance error $\eta$ except with probability $\delta$. The bound holds uniformly for one-mode squeezed vacua once $m\ge C\log(2/\delta)/\eta^2$ in the indicated parameter range.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3 — Lemma 8.26 and Eq. (163).

import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Definitions.Def_BosonicLearn_transcriptLaw
import Mathlib
import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Definitions.Def_BosonicLearn_transcriptLaw

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace LogLogJam.Supplement

theorem fixed_angle_accuracy :
    ∃ C > (0 : ℝ), ∀ η δ : ℝ, 0 < η → η ≤ 1 / 4 → 0 < δ → δ < 1 →
    ∀ m : ℕ, C * Real.log (2 / δ) / η^2 ≤ m →
    ∀ S : BosonicLearn.AdaptiveScheme 1 m ℝ, phaseCountReadouts S →
    ∃ angle : (Fin m → ℝ) → ℝ, Measurable angle ∧
      (∀ x y, (∀ i : Fin m, i.val < m / 2 → x i = y i) → angle x = angle y) ∧
      ∀ (ρ : State (Occupation (Fin 1))) (r θ : ℝ), squeezedAt ρ r θ →
        BosonicLearn.transcriptLaw S ρ.coefficients
          {x | η < LogLogJam.trDist (Real.exp (2 * r)) θ (angle x)} ≤ ENNReal.ofReal δ := by sorry

end LogLogJam.Supplement
