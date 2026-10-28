-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_eq_taylorComp_cond_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.cumulant_eq_taylorComp_cond_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:06.499819+00:00
-- url     : https://prove2.me/theorems/e57746d5-e68b-403d-82bc-29f420d708e4
-- title:
--   Cumulants as Composed Taylor Jets
-- statement:
--   This identifies cumulants with the Faà di Bruno composition of the Taylor jets of the logarithm and the Laplace transform.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel structure, and let $\mu$ be a probability measure. Let $r>0$ and assume
--
--   $$
--   \int e^{r\|x\|}\,d\mu(x)<\infty.
--   $$
--
--   For every $k\in\mathbb N$,
--
--   $$
--   \kappa_k^\mu
--   =
--   \operatorname{TaylorComp}_k\!\left(
--   \operatorname{Taylor}(\log,1),
--   \operatorname{Taylor}\!\left(z\mapsto\int e^{\langle z,x\rangle}\,d\mu(x),0\right)
--   \right).
--   $$
--
--   In Lean this is the equality between `cumulant μ k` and `FormalMultilinearSeries.taylorComp` applied to the indicated `ftaylorSeriesWithin` objects. The statement is conditional on one positive exponential moment and applies to all orders $k$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cumulant_eq_taylorComp_cond (μ : Measure E) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
--       (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (k : ℕ) :
--       cumulant μ k = (ftaylorSeriesWithin ℝ Real.log {0}ᶜ 1).taylorComp
--         (ftaylorSeriesWithin ℝ (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂μ) (Metric.ball 0 r) 0) k
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Truncation`](https://prove2.me/theorems/1997edb8-3ab3-4dc8-9655-6994bac1ddde).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Previous: [`tendsto_iteratedFDeriv_laplace_cond_closedBall`](https://prove2.me/theorems/57a5ae82-e2eb-414c-9f9c-2995a3f53149) · Next: [`tendsto_cumulant_cond_closedBall`](https://prove2.me/theorems/5a26c5c6-06d4-47bc-a7e9-de2a1a85735b).
--
--   [Source excerpt, lines 159–162](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean#L159-L162) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean#L157-L207 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation`, declaration `FunctionalInequalities.Analysis.BakryEmery.cumulant_eq_taylorComp_cond`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Truncation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.cumulant_eq_taylorComp_cond_readable (μ : Measure E) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (k : ℕ) :
    cumulant μ k = (ftaylorSeriesWithin ℝ Real.log {0}ᶜ 1).taylorComp
      (ftaylorSeriesWithin ℝ (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂μ) (Metric.ball 0 r) 0) k := by sorry
