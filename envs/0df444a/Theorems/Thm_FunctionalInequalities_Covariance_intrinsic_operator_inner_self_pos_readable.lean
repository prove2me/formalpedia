-- Prove2me | Theorems.Thm_FunctionalInequalities_Covariance_intrinsic_operator_inner_self_pos_readable
-- name    : FunctionalInequalities.Covariance.intrinsic_operator_inner_self_pos_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:21.662667+00:00
-- url     : https://prove2.me/theorems/af1259be-6217-4dce-8a0d-ab64ed2f22cf
-- title:
--   Positive Definiteness of Intrinsic Covariance
-- statement:
--   This proves positive definiteness of the intrinsic covariance operator on the affine-support direction space.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure and second-countable topology. Let $\mu$ be a probability measure on $E$ with finite second moment, and let
--
--   $$
--   V=\operatorname{direction}(\operatorname{affineSupport}(\mu)).
--   $$
--
--   For every nonzero $v\in V$,
--
--   $$
--   0<\left\langle
--   \operatorname{Cov}(\operatorname{intrinsicMeasure}(\mu))v,v
--   \right\rangle.
--   $$
--
--   The theorem supplies strict positivity after restricting the law to its intrinsic affine support, even when the ambient covariance may have null directions.
--
--   **Formalization Note** The finite second moment is expressed by `MemLp id 2`; no positive-dimensionality assumption is made.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Covariance`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem intrinsic_operator_inner_self_pos (μ : ProbabilityMeasure E)
--       (hμ : MemLp id 2 (μ : Measure E)) {v : (affineSupport μ).direction} (hv : v ≠ 0) :
--       0 < inner ℝ (operator (intrinsicMeasure μ : Measure (affineSupport μ).direction) v) v
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Covariance/Intrinsic`](https://prove2.me/theorems/541d8ad1-e32c-4fe3-bcf1-975d2f57d4f0).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81).
--
--   Supporting theorems: [`affineSupport_intrinsicMeasure`](https://prove2.me/theorems/69034b90-b400-423d-8cf5-e41038da0be1).
--
--   Previous: [`opNorm_operator_intrinsic`](https://prove2.me/theorems/71d571ba-6243-45a4-9ba5-f31b579fb453).
--
--   [Source excerpt, lines 183–185](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Covariance/Intrinsic.lean#L183-L185) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Intrinsic.lean#L181-L214 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Intrinsic`, declaration `FunctionalInequalities.Covariance.intrinsic_operator_inner_self_pos`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic

open MeasureTheory ProbabilityTheory
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E] [FiniteDimensional ℝ E]
open FunctionalInequalities.Probability
omit [CompleteSpace E]

theorem FunctionalInequalities.Covariance.intrinsic_operator_inner_self_pos_readable (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) {v : (affineSupport μ).direction} (hv : v ≠ 0) :
    0 < inner ℝ (operator (intrinsicMeasure μ : Measure (affineSupport μ).direction) v) v := by sorry
