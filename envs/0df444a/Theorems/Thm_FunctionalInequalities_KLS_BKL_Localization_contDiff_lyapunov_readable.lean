-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_contDiff_lyapunov_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.contDiff_lyapunov_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:05.042311+00:00
-- url     : https://prove2.me/theorems/4f60de76-3e6c-470a-94e3-d3d2e0b1126e
-- title:
--   Smoothness of the Localization Lyapunov Function
-- statement:
--   This auxiliary regularity theorem states that the localization Lyapunov function is infinitely differentiable.
--
--   Let $\mu$ be a probability measure on $\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))$ with compact support, and assume that $\mu$ is isotropic. Then the function
--
--   $$
--   q\longmapsto \operatorname{lyapunov}(\mu,h_c,q)
--   $$
--
--   on the localization parameter space is $C^\infty$.
--
--   The result supplies the smoothness required for generator calculations involving the Lyapunov function.
--
--   **Formalization Note.** Lean expresses infinite differentiability as `ContDiff ℝ ∞`; the function is the definition `lyapunov μ hc`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiff_lyapunov (hiso : KLS.Isotropic μ) : ContDiff ℝ ∞ (lyapunov μ hc)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Lyapunov/Basic`](https://prove2.me/theorems/1ed793bf-4e2f-450b-b764-c2de2f762cf7).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Supporting theorems: [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`contDiff_posteriorCovariance_joint`](https://prove2.me/theorems/a52d87ad-7224-4ad7-973f-f486c36649d8).
--
--   Next: [`generator_norm_sq_fst`](https://prove2.me/theorems/fff7723a-0c09-4862-bd3f-d8025b08ca9d).
--
--   [Source excerpt, lines 193–193](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Basic.lean#L193-L193) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Basic.lean#L193-L218 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Basic`, declaration `FunctionalInequalities.KLS.BKL.Localization.contDiff_lyapunov`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Basic

open scoped RealInnerProductSpace ContDiff
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.contDiff_lyapunov_readable (hiso : KLS.Isotropic μ) : ContDiff ℝ ∞ (lyapunov μ hc) := by sorry
