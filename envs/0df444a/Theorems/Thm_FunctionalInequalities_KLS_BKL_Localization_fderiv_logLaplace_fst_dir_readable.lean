-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_fderiv_logLaplace_fst_dir_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.fderiv_logLaplace_fst_dir_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:29.678051+00:00
-- url     : https://prove2.me/theorems/0fd2f814-6862-496a-98f2-b2c923618182
-- title:
--   First-Coordinate Derivative of the Posterior Log-Laplace Transform
-- statement:
--   This gives the first-coordinate derivative of the posterior log-Laplace transform.
--
--   Let $\mu$ be a compactly supported probability measure on $\mathbb{R}^n$, let $z,u\in\mathbb{R}^n$, and let $p=(c,Q)$ be a localization parameter. Define
--
--   $$
--   \Lambda_p(z)=\psi(c+z,Q)-\psi(c,Q).
--   $$
--
--   Then
--
--   $$
--   D_c\Lambda_p(z)[u]
--   =\left\langle u,\operatorname{posteriorMean}(\mu,c+z,Q)
--   -\operatorname{posteriorMean}(\mu,c,Q)\right\rangle.
--   $$
--
--   This is a partial-derivative helper for the generator calculation of the posterior log-Laplace transform.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem fderiv_logLaplace_fst_dir (z : EuclideanSpace ℝ (Fin n)) (p : Param n)
--       (u : EuclideanSpace ℝ (Fin n)) :
--       fderiv ℝ (fun q : Param n => logPartition μ (q.1 + z) q.2 - logPartition μ q.1 q.2) p (u, 0) =
--         ⟪u, posteriorMean μ (p.1 + z) p.2 - posteriorMean μ p.1 p.2⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/LogLaplaceGenerator`](https://prove2.me/theorems/590f3074-6616-4d0a-abfd-f622c05acbcf).
--
--   Definition modules: [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Probability/Posterior/LogPartition`](https://prove2.me/theorems/b716da65-348c-498f-97a9-23cbe395f8fd).
--
--   Supporting theorems: [`contDiff_logPartition_joint`](https://prove2.me/theorems/4f6af24d-bf34-47a4-ab0b-b8f6855e12d6), [`fderiv_logPartition_c_apply`](https://prove2.me/theorems/d56dc845-a2d9-42d9-b22a-bbd6ef8df04f).
--
--   Previous: [`posteriorExpectation_exp_inner_eq_exp`](https://prove2.me/theorems/66696a0d-fac3-4245-986c-d8e413dc01d5) · Next: [`generator_logLaplace_posterior`](https://prove2.me/theorems/d04c501c-dd44-4e05-9714-2e8906ff495e).
--
--   [Source excerpt, lines 274–277](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L274-L277) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L272-L298 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator`, declaration `FunctionalInequalities.KLS.BKL.Localization.fderiv_logLaplace_fst_dir`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator

open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
include hc

theorem FunctionalInequalities.KLS.BKL.Localization.fderiv_logLaplace_fst_dir_readable (z : EuclideanSpace ℝ (Fin n)) (p : Param n)
    (u : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun q : Param n => logPartition μ (q.1 + z) q.2 - logPartition μ q.1 q.2) p (u, 0) =
      ⟪u, posteriorMean μ (p.1 + z) p.2 - posteriorMean μ p.1 p.2⟫ := by sorry
