-- Prove2me | Theorems.Thm_HessianDamping_DINAVD_deriv_lyap
-- name    : HessianDamping.DINAVD.deriv_lyap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:47.366059+00:00
-- url     : https://prove2.me/theorems/d402ebcd-baf5-4cab-8ac0-21828b8d4ef8
-- title:
--   (3), p. 7 — d/dt E(t) = δ̇(t)(f(x(t)) − f(x⋆)) + δ(t)⟨∇f(x(t)), ẋ(t)⟩ + ⟨v(t), v̇(t)⟩
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $f:\mathcal H\to\mathbb R$ convex and of class $\mathcal C^2$ with a minimizer $x^\star$, $t_0>0$, and $\beta,b:[t_0,+\infty[\to\mathbb R_+$ continuous. Assume $\beta$ is differentiable on $[t_0,+\infty[$ with derivative $\dot\beta$, and that $w=b-\dot\beta-\beta/t$ is differentiable with derivative $\dot w$. Let $\alpha\ge1$ and let $x$ be a solution trajectory of $(\mathrm{DIN\text{-}AVD})_{\alpha,\beta,b}$ on $[t_0,+\infty[$. Let $\delta(t)=t^2w(t)$, and let $v$ and $E$ be as in (2):
--   $$
--   v(t)=(\alpha-1)(x(t)-x^\star)+t\big(\dot x(t)+\beta(t)\nabla f(x(t))\big),\qquad E(t)=\delta(t)\big(f(x(t))-f(x^\star)\big)+\tfrac12\|v(t)\|^2 .
--   $$
--   If $v$ has derivative $\dot v(t)$ at every $t\ge t_0$, then $E$ is differentiable on $[t_0,+\infty[$ and
--   $$
--   \frac{d}{dt}E(t)=\dot\delta(t)\big(f(x(t))-f(x^\star)\big)+\delta(t)\langle\nabla f(x(t)),\dot x(t)\rangle+\langle v(t),\dot v(t)\rangle,\qquad \dot\delta(t)=2t\,w(t)+t^2\dot w(t).
--   $$
--
--   This is the differentiation step (3) of the Lyapunov analysis of Theorem 1.
--
--   **Formalization Note** The statement carries all the standing hypotheses of Theorem 1 (convexity, the minimizer, non-negativity and continuity of $\beta,b$, $\alpha\ge1$), although the computation itself is pure calculus and uses only the differentiability of $f$, $x$, $w$ and $v$. The derivative $\dot v$ is an arbitrary map that is the derivative of $v$ (the next milestone identifies it). Derivatives are one-sided at $t_0$, taken within $[t_0,+\infty[$.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 7, proof of Theorem 1, (2)–(3)

import Mathlib
import Definitions.Def_HessianDamping_DINAVD_Setting

namespace HessianDamping.DINAVD

open Set Filter MeasureTheory

/-- (3), proof of Theorem 1, p. 7: `Ė = δ̇(f(x) − f(x⋆)) + δ⟨∇f(x), ẋ⟩ + ⟨v, v̇⟩`. -/
theorem deriv_lyap
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
    (x xd xdd : ℝ → H) (hx : IsSolution f α β b t₀ x xd xdd)
    (vd : ℝ → H)
    (hv : ∀ t ∈ Ici t₀, HasDerivWithinAt (vFun f α β xstar x xd) (vd t) (Ici t₀) t) :
    ∀ t ∈ Ici t₀, HasDerivWithinAt (lyap f α β b dβ xstar x xd)
      (deltaDeriv b β dβ dw t * (f (x t) - f xstar)
        + deltaFun b β dβ t * inner ℝ (gradient f (x t)) (xd t)
        + inner ℝ (vFun f α β xstar x xd t) (vd t)) (Ici t₀) t := by sorry

end HessianDamping.DINAVD
