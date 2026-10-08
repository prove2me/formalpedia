-- Prove2me | Theorems.Thm_HessianDamping_DINAVD_lyap_antitone
-- name    : HessianDamping.DINAVD.lyap_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:17.11398+00:00
-- url     : https://prove2.me/theorems/02a13475-1bb2-4009-9c7e-4b8c6e0a6d56
-- title:
--   (5)–(6), pp. 7–8 — under (G₂), (G₃), E(·) is non-increasing on [t₀, +∞[ and E(t) ≤ E(t₀)
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $f:\mathcal H\to\mathbb R$ convex and of class $\mathcal C^2$ with a minimizer $x^\star$, $t_0>0$, and $\beta,b:[t_0,+\infty[\to\mathbb R_+$ continuous, with $\beta$ differentiable (derivative $\dot\beta$) and $w(t)=b(t)-\dot\beta(t)-\beta(t)/t$ differentiable (derivative $\dot w$). Let $\alpha\ge1$ and let $x$ be a solution trajectory of $(\mathrm{DIN\text{-}AVD})_{\alpha,\beta,b}$ on $[t_0,+\infty[$. Assume the growth conditions
--   $$
--   (\mathcal G_2)\quad b(t)>\dot\beta(t)+\frac{\beta(t)}{t},\qquad (\mathcal G_3)\quad t\dot w(t)\le(\alpha-3)w(t)\qquad (t\ge t_0).
--   $$
--   Then the Lyapunov function $E(t)=t^2w(t)\big(f(x(t))-f(x^\star)\big)+\tfrac12\|v(t)\|^2$ of (2) is non-increasing on $[t_0,+\infty[$; in particular
--   $$
--   E(t)\le E(t_0)\qquad\text{for every } t\ge t_0 .
--   $$
--
--   Together with the non-negativity of the terms of $E$, this bound yields the rate (i) of Theorem 1.
--
--   **Formalization Note** Derivatives are one-sided at $t_0$; $E$ is the definition `lyap` of the mission's definitions file.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, pp. 7–8, proof of Theorem 1, (5), (6)

import Mathlib
import Definitions.Def_HessianDamping_DINAVD_Setting

namespace HessianDamping.DINAVD

open Set Filter MeasureTheory

/-- (5)–(6), proof of Theorem 1, pp. 7–8: `E` is non-increasing and `E(t) ≤ E(t₀)`. -/
theorem lyap_antitone
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
    AntitoneOn (lyap f α β b dβ xstar x xd) (Ici t₀) ∧
    ∀ t ∈ Ici t₀, lyap f α β b dβ xstar x xd t ≤ lyap f α β b dβ xstar x xd t₀ := by sorry

end HessianDamping.DINAVD
