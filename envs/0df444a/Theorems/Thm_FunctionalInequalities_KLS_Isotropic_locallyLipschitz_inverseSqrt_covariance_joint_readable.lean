-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_Isotropic_locallyLipschitz_inverseSqrt_covariance_joint_readable
-- name    : FunctionalInequalities.KLS.Isotropic.locallyLipschitz_inverseSqrt_covariance_joint_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:04.675807+00:00
-- url     : https://prove2.me/theorems/315359b0-06f6-4b98-a4b9-2dc033ab5cf9
-- title:
--   Local Lipschitzness of the Posterior Inverse Square Root
-- statement:
--   This statement gives a local regularity property of the diffusion coefficient used in the localization construction.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\mu$ be a probability measure with compact support. Assume that $\mu$ is isotropic, expressed by `KLS.Isotropic μ`. For each $(c,Q)\in E\times(E\to_L E)$, let $\mu_{c,Q}$ be the compact posterior and let $A(c,Q)=\operatorname{Covariance.operator}(\mu_{c,Q})$.
--
--   Then the map
--
--   $$
--   (c,Q)\longmapsto A(c,Q)^{-1/2},
--   $$
--
--   represented by `inverseSqrt`, is locally Lipschitz on the whole parameter space in the operator norm:
--
--   $$
--   \operatorname{LocallyLipschitz}\left((c,Q)\mapsto A(c,Q)^{-1/2}\right).
--   $$
--
--   The isotropy and compact-support assumptions are exactly those in the type; the statement does not assert a global Lipschitz constant.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem Isotropic.locallyLipschitz_inverseSqrt_covariance_joint (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
--       LocallyLipschitz (fun p : E × (E →L[ℝ] E) =>
--         inverseSqrt (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E)))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Posterior/Regularity`](https://prove2.me/theorems/d3a1b3f7-aa50-410c-a659-85a6897688cc).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda).
--
--   Supporting theorems: [`inner_self_pos_of_comp_eq_id`](https://prove2.me/theorems/cd7bd662-8102-4f8b-ace4-e8e741d6c4ea), [`locallyLipschitz_inverseSqrt_of_contDiff_ringInverse`](https://prove2.me/theorems/23b7714a-0376-441c-80ce-52e55886211f), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`contDiff_posteriorCovariance_joint`](https://prove2.me/theorems/a52d87ad-7224-4ad7-973f-f486c36649d8).
--
--   [Source excerpt, lines 60–63](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Posterior/Regularity.lean#L60-L63) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Posterior/Regularity.lean#L57-L78 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Posterior.Regularity`, declaration `FunctionalInequalities.KLS.Isotropic.locallyLipschitz_inverseSqrt_covariance_joint`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Regularity

open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.Isotropic.locallyLipschitz_inverseSqrt_covariance_joint_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    LocallyLipschitz (fun p : E × (E →L[ℝ] E) =>
      inverseSqrt (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))) := by sorry
