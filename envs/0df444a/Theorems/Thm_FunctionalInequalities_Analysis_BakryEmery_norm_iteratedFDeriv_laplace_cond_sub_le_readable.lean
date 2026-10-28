-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_norm_iteratedFDeriv_laplace_cond_sub_le_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_laplace_cond_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:25.796992+00:00
-- url     : https://prove2.me/theorems/b4caad6e-5213-4b24-9630-2723c2fbca35
-- title:
--   Conditional Versus Unconditional Laplace Derivative Bound
-- statement:
--   This is an operator-norm estimate for moment tensors of a conditional measure.
--
--   Let $\nu$ be a probability measure on a finite-dimensional real inner-product space $E$, let $r>0$, and assume $e^{r\|x\|}$ is integrable with respect to $\nu$. Let $s\subseteq E$ be measurable with $\nu(s)\ne0$. For every $d\in\mathbb N$,
--
--   $$\left\|D^d\!\left(z\mapsto\int e^{\langle z,x\rangle}\,d\nu[\mid s](x)\right)(0)
--   -D^d\!\left(z\mapsto\int e^{\langle z,x\rangle}\,d\nu(x)\right)(0)\right\|
--   $$
--   $$\le \left|\bigl(\nu(s)^{-1}\bigr).\operatorname{toReal}-1\right|\int\|x\|^d\,d\nu(x)+\int_{s^c}\|x\|^d\,d\nu(x).$$
--
--   Here $\nu[\mid s]$ is the conditional probability measure on $s$. The estimate quantifies the change in Laplace derivative tensors under conditioning.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_iteratedFDeriv_laplace_cond_sub_le (ν : Measure E) [IsProbabilityMeasure ν]
--       {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (d : ℕ)
--       {s : Set E} (hs : MeasurableSet s) (hs0 : ν s ≠ 0) :
--       ‖iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂(ν[|s])) 0 -
--           iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂ν) 0‖ ≤
--         |((ν s)⁻¹).toReal - 1| * ∫ x, ‖x‖ ^ d ∂ν + ∫ x in sᶜ, ‖x‖ ^ d ∂ν
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Truncation`](https://prove2.me/theorems/1997edb8-3ab3-4dc8-9655-6994bac1ddde).
--
--   Next: [`tendsto_iteratedFDeriv_laplace_cond_closedBall`](https://prove2.me/theorems/57a5ae82-e2eb-414c-9f9c-2995a3f53149).
--
--   [Source excerpt, lines 59–64](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean#L59-L64) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean#L58-L104 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation`, declaration `FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_laplace_cond_sub_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Truncation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_laplace_cond_sub_le_readable (ν : Measure E) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (d : ℕ)
    {s : Set E} (hs : MeasurableSet s) (hs0 : ν s ≠ 0) :
    ‖iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂(ν[|s])) 0 -
        iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂ν) 0‖ ≤
      |((ν s)⁻¹).toReal - 1| * ∫ x, ‖x‖ ^ d ∂ν + ∫ x in sᶜ, ‖x‖ ^ d ∂ν := by sorry
