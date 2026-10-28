-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_posteriorExpectation_exp_inner_eq_exp_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.posteriorExpectation_exp_inner_eq_exp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:52.510988+00:00
-- url     : https://prove2.me/theorems/66696a0d-fac3-4245-986c-d8e413dc01d5
-- title:
--   Exponential Formula for Posterior Expectations
-- statement:
--   This expresses an exponential posterior expectation through the log-partition function.
--
--   Let $\mu$ be a compactly supported probability measure on $\mathbb{R}^n$, let $z\in\mathbb{R}^n$, and let $q=(c,Q)$ be a localization parameter. Then
--
--   $$
--   \mathbb E_{\mu_{c,Q}}\!\left[e^{\langle z,X\rangle}\right]
--   =\exp\!\left(\psi(c+z,Q)-\psi(c,Q)\right).
--   $$
--
--   The formal statement uses `posteriorExpectation` and `logPartition`. It is the algebraic bridge between posterior exponential moments and the posterior log-Laplace transform.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem posteriorExpectation_exp_inner_eq_exp (z : EuclideanSpace ℝ (Fin n)) (q : Param n) :
--       posteriorExpectation μ q.1 q.2 (fun x => Real.exp ⟪z, x⟫) =
--         Real.exp (logPartition μ (q.1 + z) q.2 - logPartition μ q.1 q.2)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/LogLaplaceGenerator`](https://prove2.me/theorems/590f3074-6616-4d0a-abfd-f622c05acbcf).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Probability/Posterior/LogPartition`](https://prove2.me/theorems/b716da65-348c-498f-97a9-23cbe395f8fd), [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363).
--
--   Previous: [`generator_posteriorExpectation_exp_inner`](https://prove2.me/theorems/6a6bdaa6-0ece-4bfe-854e-2c005a8cead7) · Next: [`fderiv_logLaplace_fst_dir`](https://prove2.me/theorems/0fd2f814-6862-496a-98f2-b2c923618182).
--
--   [Source excerpt, lines 239–241](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L239-L241) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L237-L256 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator`, declaration `FunctionalInequalities.KLS.BKL.Localization.posteriorExpectation_exp_inner_eq_exp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator

open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
include hc

theorem FunctionalInequalities.KLS.BKL.Localization.posteriorExpectation_exp_inner_eq_exp_readable (z : EuclideanSpace ℝ (Fin n)) (q : Param n) :
    posteriorExpectation μ q.1 q.2 (fun x => Real.exp ⟪z, x⟫) =
      Real.exp (logPartition μ (q.1 + z) q.2 - logPartition μ q.1 q.2) := by sorry
