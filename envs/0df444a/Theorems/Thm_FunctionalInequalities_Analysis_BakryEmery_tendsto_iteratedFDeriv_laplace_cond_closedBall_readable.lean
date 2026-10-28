-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tendsto_iteratedFDeriv_laplace_cond_closedBall_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.tendsto_iteratedFDeriv_laplace_cond_closedBall_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:36.789526+00:00
-- url     : https://prove2.me/theorems/57a5ae82-e2eb-414c-9f9c-2995a3f53149
-- title:
--   Convergence of Truncated Laplace Derivatives
-- statement:
--   This statement proves convergence of the iterated derivatives of Laplace transforms of ball-conditioned measures.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure, and let $\nu$ be a probability measure on $E$. Let $r>0$ and assume
--
--   $$
--   \int e^{r\|x\|}\,d\nu(x)<\infty.
--   $$
--
--   For each $d\in\mathbb N$, define the Laplace transform of the conditional measure on the closed ball $\overline B(0,R)$ by
--
--   $$
--   L_R(z)=\int e^{\langle z,x\rangle}\,d\bigl(\nu[\mid\overline B(0,R)]\bigr)(x),
--   $$
--
--   and let $L(z)=\int e^{\langle z,x\rangle}\,d\nu(x)$. Then, as $R\to\infty$ through natural numbers,
--
--   $$
--   D^dL_R(0)\longrightarrow D^dL(0).
--   $$
--
--   Here convergence is in the norm of the corresponding iterated derivative spaces. This is the moment-tensor convergence statement used in truncation arguments for cumulants.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_iteratedFDeriv_laplace_cond_closedBall (ν : Measure E) [IsProbabilityMeasure ν]
--       {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (d : ℕ) :
--       Tendsto (fun R : ℕ => iteratedFDeriv ℝ d
--           (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂(ν[|Metric.closedBall (0 : E) R])) 0) atTop
--         (𝓝 (iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂ν) 0))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Truncation`](https://prove2.me/theorems/1997edb8-3ab3-4dc8-9655-6994bac1ddde).
--
--   Supporting theorems: [`norm_iteratedFDeriv_laplace_cond_sub_le`](https://prove2.me/theorems/b4caad6e-5213-4b24-9630-2723c2fbca35).
--
--   Previous: [`norm_iteratedFDeriv_laplace_cond_sub_le`](https://prove2.me/theorems/b4caad6e-5213-4b24-9630-2723c2fbca35) · Next: [`cumulant_eq_taylorComp_cond`](https://prove2.me/theorems/e57746d5-e68b-403d-82bc-29f420d708e4).
--
--   [Source excerpt, lines 118–122](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean#L118-L122) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean#L117-L155 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation`, declaration `FunctionalInequalities.Analysis.BakryEmery.tendsto_iteratedFDeriv_laplace_cond_closedBall`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Truncation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.tendsto_iteratedFDeriv_laplace_cond_closedBall_readable (ν : Measure E) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (d : ℕ) :
    Tendsto (fun R : ℕ => iteratedFDeriv ℝ d
        (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂(ν[|Metric.closedBall (0 : E) R])) 0) atTop
      (𝓝 (iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂ν) 0)) := by sorry
