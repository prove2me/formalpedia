-- Prove2me | Theorems.Thm_MoreauChance_Consistency_theorem_3_1_b
-- name    : MoreauChance.Consistency.theorem_3_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:08.100738+00:00
-- url     : https://prove2.me/theorems/d578a0a9-82a2-4320-ad8a-09cc432fe0c5
-- title:
--   Theorem 3.1 b), p. 9 — limsup ϕλk(xk) ≤ ϕ(x) for λk → 0, xk → x (and xk ⇀ x if h is weakly continuous) (14)
-- statement:
--   In the setting of Theorem 3.1 (separable Hilbert $\mathcal H$, Banach $\mathcal Y$, $\xi$ with a Lebesgue density, conic setting (9)–(10) with $\mathcal K$ closed, $\Phi$ continuous), let $(\lambda_k)$ be positive with $\lambda_k\to0$.
--
--   1. If $x_k\to x$ in norm, then
--   $$
--   \limsup_{k\to\infty}\varphi_{\lambda_k}(x_k)\le\varphi(x). \tag{14}
--   $$
--   2. If moreover the function $h$ of (10) is sequentially weakly continuous on $\mathcal H$, then (14) also holds for every sequence $x_k\rightharpoonup x$ converging weakly.
--
--   This upper estimate is the "limsup" half of the hypo-convergence of $\varphi_\lambda$ to $\varphi$; it is what shows that limits of points feasible for the regularized problems are feasible for the original one.
--
--   **Formalization Note** $\varphi_\lambda$ is defined for $\lambda>0$, so "$\lambda_k\to0$" is along positive values. The limsup is in $[0,\infty]$.
-- source:
--   van Ackooij, Pérez-Aros, Soto & Vilches, Inner Moreau envelope of nonsmooth conic chance constrained optimization problems, arXiv:2301.09803v1, p. 9, Theorem 3.1 b), Equation (14)

import Mathlib
import Definitions.Def_MoreauChance_Consistency_Basic
import Definitions.Def_MoreauChance_Consistency_Setting

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace MoreauChance.Consistency

theorem theorem_3_1_b
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : Measure.map ξ μ ≪ volume)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2))
    (lamk : ℕ → ℝ) (hlam_pos : ∀ k, 0 < lamk k) (hlam_lim : Tendsto lamk atTop (𝓝 0))
    (xk : ℕ → H) (x : H) :
    (Tendsto xk atTop (𝓝 x) →
        limsup (fun k => probFunReg C h Φ μ ξ (lamk k) (xk k)) atTop ≤ probFun K Φ μ ξ x) ∧
      (SeqWeakCont h → WeakConv xk x →
        limsup (fun k => probFunReg C h Φ μ ξ (lamk k) (xk k)) atTop ≤ probFun K Φ μ ξ x) := by sorry

end MoreauChance.Consistency
