-- Prove2me | Theorems.Thm_MeasureTheory_tendsto_integral_smooth_ball_cutoff
-- name    : MeasureTheory.tendsto_integral_smooth_ball_cutoff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T10:22:07.754876+00:00
-- url     : https://prove2.me/theorems/a161b6fe-6dfb-4462-84c5-b16fb08f106f
-- title:
--   Smooth inner ball cutoffs converge to the ball integral
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with additive Haar measure $\mu$, let $r>0$, and let $h:E\to\mathbb R$ be continuous on $\overline B_r(x)$. Let $\varepsilon_k>0$ tend to zero, and let $\theta$ be Mathlib's smooth increasing transition, equal to zero on $(-\infty,0]$ and one on $[1,\infty)$. Then
--
--   $$\lim_{k\to\infty}\int_E\theta\left(\frac{r^2-\lVert y-x\rVert^2}{\varepsilon_k}\right)h(y)\,d\mu(y)=\int_{B_r(x)}h(y)\,d\mu(y).$$
--
--   This smooth approximation of the ball indicator uses regularity only on the closed ball.
-- source:
--   Dominated-convergence specialization for the inner cutoffs used to prove the ball case of Hunter, Notes on PDEs, Theorem 1.46, printed p. 17, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. Transition: Mathlib Analysis/SpecialFunctions/SmoothTransition.lean.

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open MeasureTheory MeasureTheory.Measure Set Metric Filter Function
open scoped Topology
set_option autoImplicit false

theorem MeasureTheory.tendsto_integral_smooth_ball_cutoff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsAddHaarMeasure μ]
    {x : E} {r : ℝ} (hr : 0 < r)
    {h : E → ℝ} (hh : ContinuousOn h (closedBall x r))
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ y,
      Real.smoothTransition ((r ^ 2 - ‖y - x‖ ^ 2) / ε k) * h y ∂μ)
      atTop (𝓝 (∫ y in ball x r, h y ∂μ)) := by sorry
