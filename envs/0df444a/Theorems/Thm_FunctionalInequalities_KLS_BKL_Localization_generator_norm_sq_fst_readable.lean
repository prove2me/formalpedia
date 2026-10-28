-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_norm_sq_fst_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.generator_norm_sq_fst_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:15.386131+00:00
-- url     : https://prove2.me/theorems/fff7723a-0c09-4862-bd3f-d8025b08ca9d
-- title:
--   Generator of the Squared Linear Parameter Norm
-- statement:
--   This statement computes the localization generator applied to the squared norm of the linear parameter.
--
--   Let $\mu$ be a compactly supported isotropic probability law on $\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}n)$ and let $p=(c,Q)$ be a localization parameter. Then
--
--   $$
--   \operatorname{generator}\bigl(\mu,h_c,q\mapsto\|q_1\|^2\bigr)(p)
--   =2\left\langle c,\operatorname{cov}(\mu,p)^{-1}a(\mu;p)\right\rangle
--   +\operatorname{stdTrace}\!\left(\operatorname{cov}(\mu,p)^{-1}\right),
--   $$
--
--   where $a(\mu;p)$ is the posterior mean, `cov` is the posterior covariance operator, and `stdTrace` is the standard trace of the inverse covariance. This is an exact Lyapunov-generator identity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem generator_norm_sq_fst (hiso : KLS.Isotropic μ) (p : Param n) :
--       generator μ hc (fun q : Param n => ‖q.1‖ ^ 2) p =
--         2 * ⟪p.1, Ring.inverse (cov μ hc p) (posteriorMean μ p.1 p.2)⟫ + stdTrace (Ring.inverse (cov μ hc p))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Lyapunov/Basic`](https://prove2.me/theorems/1ed793bf-4e2f-450b-b764-c2de2f762cf7).
--
--   Definition modules: [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363), [`Analysis/Operator/HilbertSchmidt`](https://prove2.me/theorems/06361c00-f2b7-428f-bab2-caf9f49e2f34), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Supporting theorems: [`inner_self_pos_of_isPositive_of_isUnit`](https://prove2.me/theorems/8f74694a-1776-48f4-8eff-687b9d5a92eb), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`fderiv_fderiv_fst_dir`](https://prove2.me/theorems/a0e8f301-14c9-4b9b-85b4-3ddfdb159789), [`sum_bilin_inverseSqrt_eq`](https://prove2.me/theorems/7f385f3c-593c-495c-ae8d-54a94b5ade43).
--
--   Previous: [`contDiff_lyapunov`](https://prove2.me/theorems/4f60de76-3e6c-470a-94e3-d3d2e0b1126e) · Next: [`generator_hsNormSq_snd`](https://prove2.me/theorems/458648f7-5e6d-495f-af0b-3e5a75b3e463).
--
--   [Source excerpt, lines 255–257](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Basic.lean#L255-L257) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Basic.lean#L253-L280 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Basic`, declaration `FunctionalInequalities.KLS.BKL.Localization.generator_norm_sq_fst`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Basic

open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.KLS.BKL.Localization.generator_norm_sq_fst_readable (hiso : KLS.Isotropic μ) (p : Param n) :
    generator μ hc (fun q : Param n => ‖q.1‖ ^ 2) p =
      2 * ⟪p.1, Ring.inverse (cov μ hc p) (posteriorMean μ p.1 p.2)⟫ + stdTrace (Ring.inverse (cov μ hc p)) := by sorry
