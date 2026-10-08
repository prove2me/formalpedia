-- Prove2me | Theorems.Thm_HessianDamping_DINAVD_vFun_hasDerivWithinAt
-- name    : HessianDamping.DINAVD.vFun_hasDerivWithinAt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:57.534768+00:00
-- url     : https://prove2.me/theorems/3583473e-f9a3-4384-ba17-b755081cd94d
-- title:
--   Proof of Theorem 1, p. 7 — along (DIN-AVD), v̇(t) = t[β̇(t) + β(t)/t − b(t)]∇f(x(t))
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $f:\mathcal H\to\mathbb R$ convex and of class $\mathcal C^2$ with a minimizer $x^\star$, $t_0>0$, and $\beta,b:[t_0,+\infty[\to\mathbb R_+$ continuous, with $\beta$ differentiable (derivative $\dot\beta$) and $w=b-\dot\beta-\beta/t$ differentiable. Let $\alpha\ge1$ and let $x$ be a solution trajectory of
--   $$
--   \ddot x(t)+\frac{\alpha}{t}\dot x(t)+\beta(t)\nabla^2 f(x(t))\dot x(t)+b(t)\nabla f(x(t))=0
--   $$
--   on $[t_0,+\infty[$. Then $v(t)=(\alpha-1)(x(t)-x^\star)+t\big(\dot x(t)+\beta(t)\nabla f(x(t))\big)$ is differentiable on $[t_0,+\infty[$, with
--   $$
--   \dot v(t)=t\Big[\dot\beta(t)+\frac{\beta(t)}{t}-b(t)\Big]\nabla f(x(t)).
--   $$
--
--   The Hessian term of the dynamic is exactly what cancels the derivative of $t\beta(t)\nabla f(x(t))$, which makes $\dot v$ a multiple of the gradient; this is what drives the Lyapunov estimate (4).
--
--   **Formalization Note** Convexity, the minimizer, non-negativity and continuity of $\beta,b$, $\alpha\ge1$ and the differentiability of $w$ are standing hypotheses of Theorem 1 that this computation does not use. Derivatives are one-sided at $t_0$.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 7, proof of Theorem 1, display after (3)

import Mathlib
import Definitions.Def_HessianDamping_DINAVD_Setting

namespace HessianDamping.DINAVD

open Set Filter MeasureTheory

/-- Proof of Theorem 1, p. 7: along a solution, `v̇(t) = t[β̇(t) + β(t)/t − b(t)] ∇f(x(t))`. -/
theorem vFun_hasDerivWithinAt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC2 : ContDiff ℝ 2 f)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (β b dβ dw : ℝ → ℝ)
    (hβnn : ∀ t ∈ Ici t₀, 0 ≤ β t) (hbnn : ∀ t ∈ Ici t₀, 0 ≤ b t)
    (hβc : ContinuousOn β (Ici t₀)) (hbc : ContinuousOn b (Ici t₀))
    (hdβ : ∀ t ∈ Ici t₀, HasDerivWithinAt β (dβ t) (Ici t₀) t)
    (hdw : ∀ t ∈ Ici t₀, HasDerivWithinAt (wFun b β dβ) (dw t) (Ici t₀) t)
    (α : ℝ) (hα : 1 ≤ α)
    (x xd xdd : ℝ → H) (hx : IsSolution f α β b t₀ x xd xdd) :
    ∀ t ∈ Ici t₀, HasDerivWithinAt (vFun f α β xstar x xd)
      ((t * (dβ t + β t / t - b t)) • gradient f (x t)) (Ici t₀) t := by sorry

end HessianDamping.DINAVD
