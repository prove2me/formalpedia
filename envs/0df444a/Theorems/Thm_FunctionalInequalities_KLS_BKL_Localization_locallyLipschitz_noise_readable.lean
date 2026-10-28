-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_locallyLipschitz_noise_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.locallyLipschitz_noise_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:37.809732+00:00
-- url     : https://prove2.me/theorems/aa73acec-6bb4-4a4c-a7ca-0777d3c209ba
-- title:
--   Local Lipschitzness of Localization Noise Columns
-- statement:
--   This statement establishes local Lipschitzness of each noise column in the finite-dimensional localization system.
--
--   Let $n\in\mathbb N$, let $\mu$ be a probability measure on $\mathbb R^n$ represented as `EuclideanSpace ℝ (Fin n)`, and assume that its support is compact and that $\mu$ is isotropic. Let $k\in\operatorname{Fin}(n)$. For a localization parameter $p=(c,Q)$, let `noise μ hc p k` denote the $k$th noise column, whose first component is the inverse square root of the posterior covariance applied to the $k$th standard basis vector.
--
--   Then
--
--   $$
--   p\longmapsto \operatorname{noise}(\mu,h_c,p,k)
--   $$
--
--   is locally Lipschitz. The conclusion is asserted separately for every coordinate $k$ and does not provide a common global Lipschitz constant.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem locallyLipschitz_noise (hiso : KLS.Isotropic μ) (k : Fin n) :
--       LocallyLipschitz (fun p : Param n => noise μ hc p k)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74).
--
--   Definition modules: [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Supporting theorems: [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`Isotropic.locallyLipschitz_inverseSqrt_covariance_joint`](https://prove2.me/theorems/315359b0-06f6-4b98-a4b9-2dc033ab5cf9), [`contDiff_posteriorCovariance_joint`](https://prove2.me/theorems/a52d87ad-7224-4ad7-973f-f486c36649d8), [`contDiff_posteriorMean_joint`](https://prove2.me/theorems/74843a12-a6a2-460d-9106-3e5347056aaa).
--
--   Next: [`cutoffCoefficients_admissible`](https://prove2.me/theorems/b3c27db8-2231-4fb1-9cdc-cc4964163df3).
--
--   [Source excerpt, lines 89–90](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Coefficients.lean#L89-L90) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Coefficients.lean#L88-L103 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Coefficients`, declaration `FunctionalInequalities.KLS.BKL.Localization.locallyLipschitz_noise`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients

variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.locallyLipschitz_noise_readable (hiso : KLS.Isotropic μ) (k : Fin n) :
    LocallyLipschitz (fun p : Param n => noise μ hc p k) := by sorry
