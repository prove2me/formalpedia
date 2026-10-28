-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_Isotropic_exists_inverseSqrt_equiv_isotropic_standardized_readable
-- name    : FunctionalInequalities.KLS.Isotropic.exists_inverseSqrt_equiv_isotropic_standardized_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:07.318338+00:00
-- url     : https://prove2.me/theorems/590c5914-bf1c-477c-b78a-cf7e5e57e017
-- title:
--   Isotropic Standardization of a Compact Posterior
-- statement:
--   This is a canonical standardization statement related to the posterior in Equation (67) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Equation (67), p. 19.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel measurable structure. Let $\mu$ be an isotropic probability measure with compact support, let $c\in E$, and let $Q:E\to E$ be continuous linear. Then there exists a continuous linear equivalence $W:E\simeq_L E$ such that
--
--   $$W=\operatorname{inverseSqrt}\bigl(\operatorname{Cov}(\mu_{c,Q})\bigr),$$
--
--   and the pushforward by $W$ of the posterior centered at its mean is isotropic:
--
--   $$W_\#\bigl((\mu_{c,Q})\text{ translated by }-\operatorname{posteriorMean}(\mu,c,Q)\bigr)\text{ is isotropic}.$$
--
--   The posterior is `compactPosterior μ hc c Q`, and the covariance operator is `Covariance.operator`. The conclusion is existential and applies only under the compact-support and finite-dimensional hypotheses shown.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem Isotropic.exists_inverseSqrt_equiv_isotropic_standardized (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
--       ∃ W : E ≃L[ℝ] E,
--         (W : E →L[ℝ] E) = inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure E)) ∧
--         KLS.Isotropic (Probability.mapContinuousLinearEquiv
--           (Probability.translateLaw (compactPosterior μ hc c Q) (-posteriorMean μ c Q)) W)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Posterior/Standardization`](https://prove2.me/theorems/4671fb2f-bcb0-4175-82a9-3d629303664a).
--
--   Definition modules: [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363), [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533), [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda).
--
--   Supporting theorems: [`inverseSqrt_mul_mul_inverseSqrt`](https://prove2.me/theorems/88c3f67d-7fa1-4c20-b7d0-8fa8e80c182a), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`Covariance.operator_map_continuousLinearEquiv`](https://prove2.me/theorems/4b0ba356-0a64-4912-a8f7-67b0e65a1329).
--
--   [Source excerpt, lines 34–39](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Posterior/Standardization.lean#L34-L39) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Posterior/Standardization.lean#L32-L112 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Posterior.Standardization`, declaration `FunctionalInequalities.KLS.Isotropic.exists_inverseSqrt_equiv_isotropic_standardized`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Standardization

open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.Isotropic.exists_inverseSqrt_equiv_isotropic_standardized_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    ∃ W : E ≃L[ℝ] E,
      (W : E →L[ℝ] E) = inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure E)) ∧
      KLS.Isotropic (Probability.mapContinuousLinearEquiv
        (Probability.translateLaw (compactPosterior μ hc c Q) (-posteriorMean μ c Q)) W) := by sorry
