-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_logLaplace_posterior_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.generator_logLaplace_posterior_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:37.941191+00:00
-- url     : https://prove2.me/theorems/d04c501c-dd44-4e05-9714-2e8906ff495e
-- title:
--   Posterior Log-Laplace Generator Identity
-- statement:
--   This formalizes the generator form of BKL (71), cited as Lemma 4.3, p. 20, of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $n\in\mathbb N$, let $\mu$ be a probability measure on $\mathrm{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,n)$, and assume: (1) the support of $\mu$ is compact; (2) $\mu$ is isotropic in the sense of `KLS.Isotropic`. Let $z\in\mathrm{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,n)$ and let $p=(c,Q)$ be a localization parameter in `Param n`.
--
--   Define
--   $\Lambda_p(z)=\log Z_\mu(c+z,Q)-\log Z_\mu(c,Q)$, where `logPartition` is $\log Z_\mu$, and define
--   $ v=a_\mu(c+z,Q)-a_\mu(c,Q)$ using `posteriorMean`. Then
--
--   $$
--   \operatorname{generator}_{\mu}(\Lambda_{\bullet}(z))(p)
--   =-\frac12\left\langle v,\operatorname{Cov}_{\mu_p}^{-1}v\right\rangle.
--   $$
--
--   The inverse is the `Ring.inverse` of the covariance operator at $p$; no invertibility conclusion is asserted separately because isotropy and compactness are hypotheses of the identity. This is a pointwise generator formula for later localization calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem generator_logLaplace_posterior (hiso : KLS.Isotropic μ) (z : EuclideanSpace ℝ (Fin n))
--       (p : Param n) :
--       generator μ hc (fun q : Param n => logPartition μ (q.1 + z) q.2 - logPartition μ q.1 q.2) p =
--         -(1 / 2 : ℝ) * ⟪posteriorMean μ (p.1 + z) p.2 - posteriorMean μ p.1 p.2,
--           Ring.inverse (cov μ hc p) (posteriorMean μ (p.1 + z) p.2 - posteriorMean μ p.1 p.2)⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/LogLaplaceGenerator`](https://prove2.me/theorems/590f3074-6616-4d0a-abfd-f622c05acbcf).
--
--   Definition modules: [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Probability/Posterior/LogPartition`](https://prove2.me/theorems/b716da65-348c-498f-97a9-23cbe395f8fd), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Selected supporting theorems: [`inner_self_pos_of_isPositive_of_isUnit`](https://prove2.me/theorems/8f74694a-1776-48f4-8eff-687b9d5a92eb), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`fderiv_logLaplace_fst_dir`](https://prove2.me/theorems/0fd2f814-6862-496a-98f2-b2c923618182), [`generator_posteriorExpectation_exp_inner`](https://prove2.me/theorems/6a6bdaa6-0ece-4bfe-854e-2c005a8cead7), [`posteriorExpectation_exp_inner_eq_exp`](https://prove2.me/theorems/66696a0d-fac3-4245-986c-d8e413dc01d5).
--
--   Previous: [`fderiv_logLaplace_fst_dir`](https://prove2.me/theorems/0fd2f814-6862-496a-98f2-b2c923618182).
--
--   [Source excerpt, lines 303–307](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L303-L307) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 4.3, p. 20. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L300-L338 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator`, declaration `FunctionalInequalities.KLS.BKL.Localization.generator_logLaplace_posterior`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator

open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.generator_logLaplace_posterior_readable (hiso : KLS.Isotropic μ) (z : EuclideanSpace ℝ (Fin n))
    (p : Param n) :
    generator μ hc (fun q : Param n => logPartition μ (q.1 + z) q.2 - logPartition μ q.1 q.2) p =
      -(1 / 2 : ℝ) * ⟪posteriorMean μ (p.1 + z) p.2 - posteriorMean μ p.1 p.2,
        Ring.inverse (cov μ hc p) (posteriorMean μ (p.1 + z) p.2 - posteriorMean μ p.1 p.2)⟫ := by sorry
