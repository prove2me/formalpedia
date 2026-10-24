-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_covariance_sq_le_variance_mul_variance_408915f
-- name    : FunctionalInequalities.Probability.covariance_sq_le_variance_mul_variance_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:07:55.948298+00:00
-- url     : https://prove2.me/theorems/efc78852-78dd-4037-8ce8-bb1bc59ee46b
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
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/CauchySchwarz.lean#L22-L71 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.CauchySchwarz`, declaration `FunctionalInequalities.Probability.covariance_sq_le_variance_mul_variance`; the repository is private at upload time).

import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem FunctionalInequalities.Probability.covariance_sq_le_variance_mul_variance_408915f {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    covariance X Y μ ^ 2 ≤ variance X μ * variance Y μ := by sorry
