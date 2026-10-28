-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_inner_cov_apply_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.inner_cov_apply_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:50.244991+00:00
-- url     : https://prove2.me/theorems/9dacc562-afff-4880-8959-c09a4a246ec3
-- title:
--   Posterior Covariance as a Second Cumulant
-- statement:
--   This identifies the bilinear form of the posterior covariance with a second cumulant.
--
--   Let $\mu$ be a compactly supported probability measure on $\mathbb{R}^n$, let $p$ be a localization parameter, and let $x,y\in\mathbb{R}^n$. If $A(p)=\operatorname{cov}(\mu,p)$ and $\mu_p$ is the compact posterior, then
--
--   $$
--   \langle A(p)x,y\rangle
--   =\kappa_2(\mu_p)(x,y).
--   $$
--
--   The two-vector argument is represented formally by `![x, y]`. This is a reusable identification of covariance entries with cumulant data.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_cov_apply (p : Param n) (x y : EuclideanSpace ℝ (Fin n)) :
--       ⟪cov μ hc p x, y⟫ =
--         cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) 2 ![x, y]
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/CumulantDerivative`](https://prove2.me/theorems/b075fb8a-3376-43d8-a3ac-d3bc2b12f9f8).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda).
--
--   Supporting theorems: [`cumulant_two_eq_centered_moment_of_integrable_exp`](https://prove2.me/theorems/1be40a1a-f577-4044-a357-24fac041b6cb), [`memLp_of_polynomial_bound_of_integrable_exp`](https://prove2.me/theorems/c310b23c-d379-45e3-87b0-6aa7ce729818).
--
--   Previous: [`fderiv_cumulant_posterior_apply`](https://prove2.me/theorems/7e33f35a-71f2-43a6-bb75-a119f0e67849).
--
--   [Source excerpt, lines 195–197](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantDerivative.lean#L195-L197) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantDerivative.lean#L194-L217 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative`, declaration `FunctionalInequalities.KLS.BKL.Localization.inner_cov_apply`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.inner_cov_apply_readable (p : Param n) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪cov μ hc p x, y⟫ =
      cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) 2 ![x, y] := by sorry
