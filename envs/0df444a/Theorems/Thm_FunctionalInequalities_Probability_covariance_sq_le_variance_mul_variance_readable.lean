-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_covariance_sq_le_variance_mul_variance_readable
-- name    : FunctionalInequalities.Probability.covariance_sq_le_variance_mul_variance_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:22.933222+00:00
-- url     : https://prove2.me/theorems/12e81134-7f94-480d-a9f0-74ef2af40616
-- title:
--   Covariance Cauchy–Schwarz Inequality
-- statement:
--   This statement gives the covariance form of the Cauchy–Schwarz inequality for square-integrable real random variables.
--
--   Let $(\Omega,\mu)$ be a probability space and let $X,Y:\Omega\to\mathbb{R}$ satisfy $X,Y\in L^2(\mu)$, expressed by `MemLp X 2 μ` and `MemLp Y 2 μ`. Then
--
--   $$
--   \operatorname{Cov}_{\mu}(X,Y)^2
--   \le
--   \operatorname{Var}_{\mu}(X)\,\operatorname{Var}_{\mu}(Y).
--   $$
--
--   This is a general measure-theoretic inequality on an arbitrary measurable space and is used as a deterministic covariance estimate in posterior calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem covariance_sq_le_variance_mul_variance {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
--       covariance X Y μ ^ 2 ≤ variance X μ * variance Y μ
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Covariance/CauchySchwarz`](https://prove2.me/theorems/609822dd-0643-4f61-936f-db8283b6fe24).
--
--   [Source excerpt, lines 23–24](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Covariance/CauchySchwarz.lean#L23-L24) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/CauchySchwarz.lean#L22-L71 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.CauchySchwarz`, declaration `FunctionalInequalities.Probability.covariance_sq_le_variance_mul_variance`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_CauchySchwarz

open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]

theorem FunctionalInequalities.Probability.covariance_sq_le_variance_mul_variance_readable {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    covariance X Y μ ^ 2 ≤ variance X μ * variance Y μ := by sorry
