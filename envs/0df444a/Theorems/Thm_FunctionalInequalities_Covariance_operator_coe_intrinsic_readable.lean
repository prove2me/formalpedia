-- Prove2me | Theorems.Thm_FunctionalInequalities_Covariance_operator_coe_intrinsic_readable
-- name    : FunctionalInequalities.Covariance.operator_coe_intrinsic_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:18.476154+00:00
-- url     : https://prove2.me/theorems/fe1dea64-17ba-41d3-baa5-d22dd2d8805b
-- title:
--   Ambient Covariance Operator on Intrinsic Directions
-- statement:
--   This states that the ambient covariance operator restricts to the intrinsic covariance operator on the affine-support direction space.
--
--   Let $E$ be a complete, finite-dimensional, second-countable real inner-product space with its Borel measurable structure. Let $\mu$ be a probability measure with finite second moment, let
--
--   $$
--   V=\operatorname{direction}(\operatorname{affineSupport}(\mu)),
--   $$
--
--   and let $v\in V$. Then, after coercing the intrinsic vector and intrinsic covariance output into $E$,
--
--   $$
--   \operatorname{Cov}(\mu)(v)
--   =
--   \operatorname{Cov}(\operatorname{intrinsicMeasure}(\mu))(v).
--   $$
--
--   This is the operator-level form of the ambient–intrinsic covariance correspondence and supports norm and positivity comparisons.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Covariance`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem operator_coe_intrinsic (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E))
--       (v : (affineSupport μ).direction) :
--       operator (μ : Measure E) v =
--         (operator (intrinsicMeasure μ : Measure (affineSupport μ).direction) v : E)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Covariance/Intrinsic`](https://prove2.me/theorems/541d8ad1-e32c-4fe3-bcf1-975d2f57d4f0).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81).
--
--   Supporting theorems: [`bilin_intrinsic`](https://prove2.me/theorems/1674ab9b-187e-47f3-8b54-7cbcd2655548).
--
--   Previous: [`bilin_intrinsic`](https://prove2.me/theorems/1674ab9b-187e-47f3-8b54-7cbcd2655548) · Next: [`opNorm_operator_intrinsic`](https://prove2.me/theorems/71d571ba-6243-45a4-9ba5-f31b579fb453).
--
--   [Source excerpt, lines 128–131](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Covariance/Intrinsic.lean#L128-L131) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Intrinsic.lean#L126-L152 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Intrinsic`, declaration `FunctionalInequalities.Covariance.operator_coe_intrinsic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic

open MeasureTheory ProbabilityTheory
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E] [FiniteDimensional ℝ E]
open FunctionalInequalities.Probability

theorem FunctionalInequalities.Covariance.operator_coe_intrinsic_readable (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E))
    (v : (affineSupport μ).direction) :
    operator (μ : Measure E) v =
      (operator (intrinsicMeasure μ : Measure (affineSupport μ).direction) v : E) := by sorry
