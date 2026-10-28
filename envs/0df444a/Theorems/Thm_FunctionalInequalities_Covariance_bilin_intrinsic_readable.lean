-- Prove2me | Theorems.Thm_FunctionalInequalities_Covariance_bilin_intrinsic_readable
-- name    : FunctionalInequalities.Covariance.bilin_intrinsic_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:13.566395+00:00
-- url     : https://prove2.me/theorems/1674ab9b-187e-47f3-8b54-7cbcd2655548
-- title:
--   Ambient and Intrinsic Covariance Bilinear Forms
-- statement:
--   This identifies the ambient covariance bilinear form with the intrinsic covariance bilinear form on the affine-support direction space.
--
--   Let $E$ be a complete, finite-dimensional, second-countable real inner-product space with its Borel measurable structure. Let $\mu$ be a probability measure on $E$ satisfying
--
--   $$
--   \operatorname{id}\in L^2(\mu).
--   $$
--
--   Let $V$ be the direction of the affine support of $\mu$, and let $v,w\in V$. Then
--
--   $$
--   \operatorname{Cov}(\operatorname{intrinsicMeasure}(\mu))(v,w)
--   =
--   \operatorname{Cov}(\mu)(v,w),
--   $$
--
--   where the right-hand side views $v,w$ as vectors in $E$.
--
--   This is the basic covariance identity for intrinsic coordinates and is reusable in comparisons between ambient and affine-support formulations.
--
--   **Formalization Note** The intrinsic law is `intrinsicMeasure μ`, and the second-moment assumption is the explicit `MemLp id 2` hypothesis.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Covariance`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem bilin_intrinsic (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E))
--       (v w : (affineSupport μ).direction) :
--       covarianceBilin (intrinsicMeasure μ : Measure (affineSupport μ).direction) v w =
--         covarianceBilin (μ : Measure E) v w
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Covariance/Intrinsic`](https://prove2.me/theorems/541d8ad1-e32c-4fe3-bcf1-975d2f57d4f0).
--
--   Definition modules: [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81).
--
--   Next: [`operator_coe_intrinsic`](https://prove2.me/theorems/fe1dea64-17ba-41d3-baa5-d22dd2d8805b).
--
--   [Source excerpt, lines 106–109](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Covariance/Intrinsic.lean#L106-L109) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Intrinsic.lean#L104-L124 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Intrinsic`, declaration `FunctionalInequalities.Covariance.bilin_intrinsic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic

open MeasureTheory ProbabilityTheory
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E] [FiniteDimensional ℝ E]
open FunctionalInequalities.Probability

theorem FunctionalInequalities.Covariance.bilin_intrinsic_readable (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E))
    (v w : (affineSupport μ).direction) :
    covarianceBilin (intrinsicMeasure μ : Measure (affineSupport μ).direction) v w =
      covarianceBilin (μ : Measure E) v w := by sorry
