-- Prove2me | Theorems.Thm_HessianDamping_DINAVD_integral_bounds
-- name    : HessianDamping.DINAVD.integral_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:18.35893+00:00
-- url     : https://prove2.me/theorems/3e9aaf26-ca3d-4672-81bf-6fb55a61b552
-- title:
--   Proof of Theorem 1, p. 8 — ∫ β(t)δ(t)‖∇f(x(t))‖² dt ≤ E(t₀) and ∫ t((α − 3)w(t) − tẇ(t))(f(x(t)) − f(x⋆)) dt ≤ E(t₀)
-- statement:
--   Under the hypotheses of Theorem 1 — $\mathcal H$ a real Hilbert space, $f$ convex of class $\mathcal C^2$ with a minimizer $x^\star$, $t_0>0$, $\beta,b\ge0$ continuous on $[t_0,+\infty[$, $\beta$ differentiable, $w(t)=b(t)-\dot\beta(t)-\beta(t)/t$ differentiable, $\alpha\ge1$, $x$ a solution trajectory of $(\mathrm{DIN\text{-}AVD})_{\alpha,\beta,b}$, and the growth conditions $(\mathcal G_2)$ $b>\dot\beta+\beta/t$ and $(\mathcal G_3)$ $t\dot w\le(\alpha-3)w$ on $[t_0,+\infty[$ — let $\delta(t)=t^2w(t)$ and let $E$ be the Lyapunov function (2). Then both functions below are integrable on $[t_0,+\infty[$, and
--   $$
--   \int_{t_0}^{+\infty}\beta(t)\delta(t)\|\nabla f(x(t))\|^2\,dt\le E(t_0)<+\infty,
--   $$
--   $$
--   \int_{t_0}^{+\infty}t\big((\alpha-3)w(t)-t\dot w(t)\big)\big(f(x(t))-f(x^\star)\big)\,dt\le E(t_0)<+\infty .
--   $$
--
--   These are the integrated forms of (4), which give conclusions (ii) and (iii) of Theorem 1.
--
--   **Formalization Note** Integrability on $[t_0,+\infty[$ is stated explicitly, so the integral bounds do not rely on the zero value Lean assigns to the integral of a non-integrable function.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 8, proof of Theorem 1, the two integral displays

import Mathlib
import Definitions.Def_HessianDamping_DINAVD_Setting

namespace HessianDamping.DINAVD

open Set Filter MeasureTheory

/-- Proof of Theorem 1, p. 8: the integrated forms of (4). -/
theorem integral_bounds
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
    (hG₃ : ∀ t ∈ Ici t₀, t * dw t ≤ (α - 3) * wFun b β dβ t) :
    IntegrableOn (fun t => β t * deltaFun b β dβ t * ‖gradient f (x t)‖ ^ 2) (Ici t₀) ∧
    ∫ t in Ici t₀, β t * deltaFun b β dβ t * ‖gradient f (x t)‖ ^ 2
      ≤ lyap f α β b dβ xstar x xd t₀ ∧
    IntegrableOn
      (fun t => t * ((α - 3) * wFun b β dβ t - t * dw t) * (f (x t) - f xstar)) (Ici t₀) ∧
    ∫ t in Ici t₀, t * ((α - 3) * wFun b β dβ t - t * dw t) * (f (x t) - f xstar)
      ≤ lyap f α β b dβ xstar x xd t₀ := by sorry

end HessianDamping.DINAVD
