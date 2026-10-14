-- Prove2me | Theorems.Thm_GPhNGIDiffusion_OccupationCLT_theorem_1_3
-- name    : GPhNGIDiffusion.OccupationCLT.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:28.312328+00:00
-- url     : https://prove2.me/theorems/835875d0-cfdb-4aeb-b522-bcbb4c440c0a
-- title:
--   Theorem 1.3 (CLT), p. 4 — √t[E^x_t(h) − μ(h)] ⇒ N(0, μ(|σ′∇f|²)), with μ(|σ′∇f|²) ≤ C∥h∥²_∞
-- statement:
--   Let $(X_t)_{t\ge0}$ be the limiting diffusion (1.1) of the $G/Ph/n+GI$ queue in the Halfin–Whitt regime, with invariant probability measure $\mu$, and for $x\in\mathbb R^d$ let $\mathcal E^x_t(h)=\frac1t\int_0^th(X^x_s)\,ds$ be the empirical average of $h$ along the path started at $x$. Let $f$ be the solution (3.2) of the Stein equation $\mathcal Af=h-\mu(h)$ (3.1).
--
--   There is a constant $C>0$ such that for every bounded measurable $h:\mathbb R^d\to\mathbb R$:
--   1. $f$ is differentiable and
--   $$
--   \mu(|\sigma'\nabla f|^2)\le C\|h\|_\infty^2<\infty ;
--   $$
--   2. for every $x\in\mathbb R^d$,
--   $$
--   \sqrt t\,\big[\mathcal E^x_t(h)-\mu(h)\big]\Rightarrow\mathcal N\big(0,\mu(|\sigma'\nabla f|^2)\big)\qquad(t\to\infty).
--   $$
--
--   The theorem quantifies the fluctuations of time averages of the diffusion around the stationary mean, at rate $\sqrt t$ and for every starting point, with an explicit variance given by the Stein solution.
--
--   **Formalization Note** Weak convergence is the paper's definition (§1.4): $\mathbb E\varphi(Y_t)\to\mathbb E\varphi(Y_\infty)$ for every bounded continuous $\varphi$, along real $t\to\infty$. $\mathcal N(0,0)$ is the point mass at $0$. The variance is the lower Lebesgue integral $\int|\sigma'\nabla f|^2d\mu$, finite by item 1. The constant is uniform in $h$ (the paper's proof takes it from Proposition 3.1 and Lemma A.1, which do not depend on $h$). Differentiability of $f$ is stated so that $\nabla f$ is the true gradient.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 4, Theorem 1.3 (proof pp. 16–19)

import Mathlib
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Occupation
open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace GPhNGIDiffusion.OccupationCLT

/-- Theorem 1.3 (CLT), p. 4. For bounded measurable `h` and every starting point `x`,
`√t [E^x_t(h) − μ(h)]` converges weakly to `N(0, μ(|σ′∇f|²))` as `t → ∞`, where `f` is the
solution (3.2) of the Stein equation (3.1); moreover `f` is differentiable and
`μ(|σ′∇f|²) ≤ C∥h∥²_∞ < ∞` with `C` independent of `h`. Weak convergence is
`E φ(Y_t) → E φ(Y_∞)` for every bounded continuous `φ` (§1.4). -/
theorem theorem_1_3 {d : ℕ} (M : Model d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → E d) (X : E d → ℝ≥0 → Ω → E d) (hX : IsDiffusion M P B X)
    (μ : Measure (E d)) [IsProbabilityMeasure μ] (hμ : IsInvariant P X μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : E d → ℝ, Measurable h → (∃ K : ℝ, ∀ y, |h y| ≤ K) →
      Differentiable ℝ (steinSol P X μ h) ∧
      (∫⁻ y, ‖mat M.σᵀ (gradient (steinSol P X μ h) y)‖ₑ ^ 2 ∂μ
          ≤ ENNReal.ofReal (C * supNorm h ^ 2)) ∧
      ∀ (x : E d) (φ : BoundedContinuousFunction ℝ ℝ),
        Tendsto
          (fun t : ℝ≥0 => ∫ ω, φ (Real.sqrt t * (occAvg X h x t ω - ∫ y, h y ∂μ)) ∂P)
          atTop
          (𝓝 (∫ z, φ z ∂(gaussianReal 0
            (∫⁻ y, ‖mat M.σᵀ (gradient (steinSol P X μ h) y)‖ₑ ^ 2 ∂μ).toNNReal))) := by sorry

end GPhNGIDiffusion.OccupationCLT
