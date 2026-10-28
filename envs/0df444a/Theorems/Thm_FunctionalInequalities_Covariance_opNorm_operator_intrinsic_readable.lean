-- Prove2me | Theorems.Thm_FunctionalInequalities_Covariance_opNorm_operator_intrinsic_readable
-- name    : FunctionalInequalities.Covariance.opNorm_operator_intrinsic_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:20.4408+00:00
-- url     : https://prove2.me/theorems/71d571ba-6243-45a4-9ba5-f31b579fb453
-- title:
--   Equality of Ambient and Intrinsic Covariance Norms
-- statement:
--   This proves equality of the operator norms of the ambient and intrinsic covariance operators.
--
--   Let $E$ be a complete, finite-dimensional, second-countable real inner-product space with its Borel measurable structure, and let $\mu$ be a probability measure on $E$ with finite second moment. If $V$ is the direction of the affine support of $\mu$, then
--
--   $$
--   \left\|\operatorname{Cov}(\operatorname{intrinsicMeasure}(\mu))\right\|
--   =
--   \left\|\operatorname{Cov}(\mu)\right\|.
--   $$
--
--   The intrinsic operator acts on $V$, while the ambient operator acts on $E$.
--
--   This equality allows operator-norm estimates to be transferred between intrinsic and ambient formulations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Covariance`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem opNorm_operator_intrinsic (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E)) :
--       ‖operator (intrinsicMeasure μ : Measure (affineSupport μ).direction)‖ =
--         ‖operator (μ : Measure E)‖
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Covariance/Intrinsic`](https://prove2.me/theorems/541d8ad1-e32c-4fe3-bcf1-975d2f57d4f0).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81).
--
--   Supporting theorems: [`operator_coe_intrinsic`](https://prove2.me/theorems/fe1dea64-17ba-41d3-baa5-d22dd2d8805b).
--
--   Previous: [`operator_coe_intrinsic`](https://prove2.me/theorems/fe1dea64-17ba-41d3-baa5-d22dd2d8805b) · Next: [`intrinsic_operator_inner_self_pos`](https://prove2.me/theorems/af1259be-6217-4dce-8a0d-ab64ed2f22cf).
--
--   [Source excerpt, lines 155–157](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Covariance/Intrinsic.lean#L155-L157) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Intrinsic.lean#L154-L179 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Intrinsic`, declaration `FunctionalInequalities.Covariance.opNorm_operator_intrinsic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic

open MeasureTheory ProbabilityTheory
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E] [FiniteDimensional ℝ E]
open FunctionalInequalities.Probability

theorem FunctionalInequalities.Covariance.opNorm_operator_intrinsic_readable (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E)) :
    ‖operator (intrinsicMeasure μ : Measure (affineSupport μ).direction)‖ =
      ‖operator (μ : Measure E)‖ := by sorry
