-- Prove2me | Theorems.Thm_LogLogJam_Supplement_split_readout_accuracy
-- name    : LogLogJam.Supplement.split_readout_accuracy
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-26T09:27:17.164975+00:00
-- url     : https://prove2.me/theorems/2302fbce-e2f6-4d0d-9059-f4ba72c24a3f
-- title:
--   Phase and photon-count accuracy on the two prescribed batches
-- statement:
--   For $0<\eta\le1/4$ and $0<\delta<1$, $m\ge C\log(2/\delta)/\eta^2$ copies suffice for two nonadaptive one-mode measurements. The first half uses canonical phase and gives a measurable angle estimate of error at most $\eta$ in the equal-squeezing trace metric. The second half counts photons and gives a nonnegative mean estimate of error at most $\eta\cosh r\sinh r$. Each bound has failure probability at most $\delta$ under the same physical transcript law, uniformly over squeezing and angle. The two estimates use only their prescribed blocks.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3 — Lemmas 8.26–8.27.

import Mathlib
import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Definitions.Def_BosonicLearn_transcriptLaw

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace LogLogJam.Supplement

theorem split_readout_accuracy :
    ∃ C > (0 : ℝ), ∀ η δ : ℝ, 0 < η → η ≤ 1 / 4 → 0 < δ → δ < 1 →
    ∀ m : ℕ, C * Real.log (2 / δ) / η ^ 2 ≤ m →
    ∃ (S : BosonicLearn.AdaptiveScheme 1 m ℝ)
      (angle mean : (Fin m → ℝ) → ℝ),
      phaseCountReadouts S ∧ Measurable angle ∧ Measurable mean ∧
      (∀ x, 0 ≤ mean x) ∧
      (∀ x y, (∀ i : Fin m, i.val < m / 2 → x i = y i) → angle x = angle y) ∧
      (∀ x y, (∀ i : Fin m, m / 2 ≤ i.val → x i = y i) → mean x = mean y) ∧
      ∀ (ρ : State (Occupation (Fin 1))) (r θ : ℝ), squeezedAt ρ r θ →
      (BosonicLearn.transcriptLaw S ρ.coefficients
        {x | η < LogLogJam.trDist (Real.exp (2 * r)) θ (angle x)} ≤ ENNReal.ofReal δ) ∧
      (BosonicLearn.transcriptLaw S ρ.coefficients
        {x | η * Real.cosh r * Real.sinh r < |mean x - Real.sinh r ^ 2|} ≤ ENNReal.ofReal δ) := by sorry

end LogLogJam.Supplement
