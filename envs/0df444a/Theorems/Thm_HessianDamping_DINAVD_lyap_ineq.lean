-- Prove2me | Theorems.Thm_HessianDamping_DINAVD_lyap_ineq
-- name    : HessianDamping.DINAVD.lyap_ineq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:09.363061+00:00
-- url     : https://prove2.me/theorems/1f790109-d0e7-4aac-966e-bec09a3d883d
-- title:
--   (4), p. 7 — d/dt E(t) + β(t)δ(t)‖∇f(x(t))‖² + [(α − 1)δ(t)/t − δ̇(t)](f(x(t)) − f(x⋆)) ≤ 0 under (G₂)
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $f:\mathcal H\to\mathbb R$ convex and of class $\mathcal C^2$ with a minimizer $x^\star$, $t_0>0$, and $\beta,b:[t_0,+\infty[\to\mathbb R_+$ continuous, with $\beta$ differentiable (derivative $\dot\beta$) and $w(t)=b(t)-\dot\beta(t)-\beta(t)/t$ differentiable (derivative $\dot w$). Let $\alpha\ge1$, let $x$ be a solution trajectory of $(\mathrm{DIN\text{-}AVD})_{\alpha,\beta,b}$ on $[t_0,+\infty[$, and assume the growth condition
--   $$
--   (\mathcal G_2)\qquad b(t)>\dot\beta(t)+\frac{\beta(t)}{t}\quad (t\ge t_0).
--   $$
--   Let $\delta(t)=t^2w(t)$, $\dot\delta(t)=2tw(t)+t^2\dot w(t)$, and let $E$ be the Lyapunov function (2). If $E$ has derivative $\frac{d}{dt}E(t)$ at every $t\ge t_0$, then for every $t\ge t_0$
--   $$
--   \frac{d}{dt}E(t)+\beta(t)\delta(t)\|\nabla f(x(t))\|^2+\Big[\frac{\alpha-1}{t}\delta(t)-\dot\delta(t)\Big]\big(f(x(t))-f(x^\star)\big)\le 0 .
--   $$
--
--   This is the key differential inequality (4) of the proof of Theorem 1; combined with $(\mathcal G_3)$ it shows that $E$ is non-increasing.
--
--   **Formalization Note** The derivative of $E$ is an arbitrary map that is the derivative of $E$ within $[t_0,+\infty[$ (it is unique there). Derivatives are one-sided at $t_0$.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 7, proof of Theorem 1, (4)

import Mathlib
import Definitions.Def_HessianDamping_DINAVD_Setting

namespace HessianDamping.DINAVD

open Set Filter MeasureTheory

/-- (4), proof of Theorem 1, p. 7. -/
theorem lyap_ineq
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
    (hG₂ : ∀ t ∈ Ici t₀, dβ t + β t / t < b t)
    (dE : ℝ → ℝ)
    (hE : ∀ t ∈ Ici t₀, HasDerivWithinAt (lyap f α β b dβ xstar x xd) (dE t) (Ici t₀) t) :
    ∀ t ∈ Ici t₀,
      dE t + β t * deltaFun b β dβ t * ‖gradient f (x t)‖ ^ 2
        + ((α - 1) / t * deltaFun b β dβ t - deltaDeriv b β dβ dw t) * (f (x t) - f xstar)
        ≤ 0 := by sorry

end HessianDamping.DINAVD
