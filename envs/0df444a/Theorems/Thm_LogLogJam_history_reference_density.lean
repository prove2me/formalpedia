-- Prove2me | Theorems.Thm_LogLogJam_history_reference_density
-- name    : LogLogJam.history_reference_density
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:26:30.472235+00:00
-- url     : https://prove2.me/theorems/73fb33cf-cb5b-515a-80d7-4661990ac67b
-- title:
--   Common reference measure and Gaussian likelihood on physical protocol histories
-- statement:
--   At any stage of a randomized adaptive Gaussian protocol there is a sigma-finite measure on histories with physical seeds, chosen independently of squeezing and angle. For every squeezing parameter greater than one, the product of the one-round outcome densities is positive and continuously differentiable in the angle, periodic with period π, measurable in the history, and integrates to one. Integration against that likelihood realizes the recursive law for every nonnegative test function measurable on the physical histories. The reference measure combines the state-independent seed transitions and Lebesgue readout measures.
-- source:
--   https://arxiv.org/abs/2607.12983; Sections 5.2–5.5, likelihood of the observed history in Lemmas 5.4, 5.5, and 5.9.

import Definitions.Def_LogLogJam_GaussProtocol

open MeasureTheory
open scoped ENNReal

namespace LogLogJam

/-- The seed kernels and Lebesgue readouts supply one dominating measure on physical
histories, independent of the angle and squeezing. The likelihood is the product
of the actual conditional Gaussian densities. The final clause identifies the
recursive transcript expectation on all nonnegative observable functions whose
restrictions to the support are measurable. -/
theorem history_reference_density {T : ℕ} (P : GaussProtocol T) (t : ℕ) (ht : t ≤ T) :
    let G := {H : Hist t // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)}
    ∃ μ : Measure G, SigmaFinite μ ∧ ∀ l : ℝ, 1 < l →
      (∀ (s : ℝ) (H : G), 0 < histDens l s H.1) ∧
      (∀ (s : ℝ) (H : G), histDens l (s+Real.pi) H.1 = histDens l s H.1) ∧
      (∀ H : G, ContDiff ℝ 1 (fun s => histDens l s H.1)) ∧
      (∀ s : ℝ, Measurable (fun H : G => histDens l s H.1)) ∧
      (∀ s : ℝ, ∫⁻ H : G, ENNReal.ofReal (histDens l s H.1) ∂μ = 1) ∧
      (∀ (s : ℝ) (Φ : Hist t → ℝ≥0∞), Measurable (fun H : G => Φ H.1) →
        histInt l s P t Φ = ∫⁻ H : G, ENNReal.ofReal (histDens l s H.1) * Φ H.1 ∂μ) := by sorry

end LogLogJam
