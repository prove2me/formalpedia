-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_inner_cumulantVector_single_ringInverse_cumulantVector_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.inner_cumulantVector_single_ringInverse_cumulantVector_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:12.911085+00:00
-- url     : https://prove2.me/theorems/9237a40c-7f1f-4233-8865-0d20c1925f94
-- title:
--   Singleton Cumulant Allocation Identity
-- statement:
--   This formalizes the singleton allocation identity in Theorem 4.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), cited at p. 21.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\mu$ be a compactly supported probability measure on $E$. Assume that the covariance operator $A=\operatorname{Cov}(\mu)$ is a unit in the relevant operator ring, so that $A^{-1}$ is available. For every finite list $h_s$ in $E$ and every $w\in E$,
--
--   $$\left\langle \kappa_2(w,\cdot),A^{-1}\kappa_{|h_s|+1}(h_s,\cdot)\right\rangle
--   =\kappa_{|h_s|+1}(h_s,w).$$
--
--   In Lean, the cumulant vectors are represented by `cumulantVector`, the covariance operator by `Covariance.operator`, and the inverse by `Ring.inverse`. The statement is a reusable reduction of a covariance-inverse pairing to a higher cumulant.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_cumulantVector_single_ringInverse_cumulantVector (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) (hA : IsUnit (Covariance.operator (μ : Measure E)))
--       (hs : List E) (w : E) :
--       ⟪cumulantVector (μ : Measure E) [w],
--           Ring.inverse (Covariance.operator (μ : Measure E)) (cumulantVector (μ : Measure E) hs)⟫ =
--         cumulant (μ : Measure E) (hs.length + 1) (Fin.snoc (fun i => hs.get i) w)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Local`](https://prove2.me/theorems/7a0cd01c-3ad0-460b-af3d-e088447d401d).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Supporting theorems: [`cumulant_two_eq_centered_moment_of_integrable_exp`](https://prove2.me/theorems/1be40a1a-f577-4044-a357-24fac041b6cb), [`memLp_of_polynomial_bound_of_integrable_exp`](https://prove2.me/theorems/c310b23c-d379-45e3-87b0-6aa7ce729818).
--
--   Previous: [`iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact`](https://prove2.me/theorems/c850afc5-a923-4019-b001-39ff0f56dd9b).
--
--   [Source excerpt, lines 660–665](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L660-L665) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L657-L721 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local`, declaration `FunctionalInequalities.Analysis.BakryEmery.inner_cumulantVector_single_ringInverse_cumulantVector`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.inner_cumulantVector_single_ringInverse_cumulantVector_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hA : IsUnit (Covariance.operator (μ : Measure E)))
    (hs : List E) (w : E) :
    ⟪cumulantVector (μ : Measure E) [w],
        Ring.inverse (Covariance.operator (μ : Measure E)) (cumulantVector (μ : Measure E) hs)⟫ =
      cumulant (μ : Measure E) (hs.length + 1) (Fin.snoc (fun i => hs.get i) w) := by sorry
