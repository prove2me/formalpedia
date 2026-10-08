-- Prove2me | Theorems.Thm_HessianDamping_DINAVD_theorem_1
-- name    : HessianDamping.DINAVD.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:03.344486+00:00
-- url     : https://prove2.me/theorems/e2c65dd4-969e-42ee-9365-3fa9a4403d72
-- title:
--   Theorem 1, pp. 6–7 — under (G₂), (G₃), w > 0, f(x(t)) − min f = O(1/(t²w(t))), and two weighted integrals are finite
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $f:\mathcal H\to\mathbb R$ a convex function of class $\mathcal C^2$ with $\operatorname{argmin}_{\mathcal H}f\neq\emptyset$, $t_0>0$, and $\beta,b:[t_0,+\infty[\to\mathbb R_+$ non-negative continuous functions (the standing assumptions (H)). Assume that $\beta$ is differentiable with derivative $\dot\beta$, set
--   $$
--   w(t):=b(t)-\dot\beta(t)-\frac{\beta(t)}{t},
--   $$
--   and assume that $w$ is differentiable with derivative $\dot w$. Take $\alpha\ge1$ and let $x:[t_0,+\infty[\to\mathcal H$ be a solution trajectory of
--   $$
--   (\mathrm{DIN\text{-}AVD})_{\alpha,\beta,b}\qquad \ddot x(t)+\frac{\alpha}{t}\dot x(t)+\beta(t)\nabla^2 f(x(t))\dot x(t)+b(t)\nabla f(x(t))=0 .
--   $$
--   Suppose that for all $t\ge t_0$ the growth conditions
--   $$
--   (\mathcal G_2)\quad b(t)>\dot\beta(t)+\frac{\beta(t)}{t},\qquad (\mathcal G_3)\quad t\dot w(t)\le(\alpha-3)w(t)
--   $$
--   hold. Then $w(t)>0$ for all $t\ge t_0$, and
--
--   1. $f(x(t))-\min_{\mathcal H}f=\mathcal O\!\left(\dfrac{1}{t^2w(t)}\right)$ as $t\to+\infty$;
--   2. $\displaystyle\int_{t_0}^{+\infty}t^2\beta(t)w(t)\|\nabla f(x(t))\|^2\,dt<+\infty$;
--   3. $\displaystyle\int_{t_0}^{+\infty}t\big((\alpha-3)w(t)-t\dot w(t)\big)\big(f(x(t))-\min_{\mathcal H}f\big)\,dt<+\infty$.
--
--   This is the general convergence-rate theorem for inertial dynamics with asymptotically vanishing damping and Hessian-driven damping: specializing $\beta$ and $b$ recovers the $\mathcal O(1/t^2)$ rate of the continuous Nesterov dynamic and, for $\beta>0$, adds the fast integrability of the gradients.
--
--   **Formalization Note** $\operatorname{argmin}f\neq\emptyset$ is encoded by a point $x^\star$ with $f(x^\star)\le f(y)$ for all $y$, so $\min_{\mathcal H}f=f(x^\star)$. The derivatives $\dot\beta$, $\dot w$ are explicit maps tied to $\beta$, $w$ by derivative hypotheses on $[t_0,+\infty[$ (the page writes $\dot\beta$ and $\dot w$, so it presupposes both exist). The trajectory is a map $\mathbb R\to\mathcal H$ whose values before $t_0$ are irrelevant; all derivatives are one-sided at $t_0$. "$<+\infty$" is integrability on $[t_0,+\infty[$; both integrands are non-negative under the hypotheses. The big-O is along `atTop` with constants depending on all the data.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, pp. 6–7, Theorem 1 (with (H), p. 2, and (1), p. 6)

import Mathlib
import Definitions.Def_HessianDamping_DINAVD_Setting

namespace HessianDamping.DINAVD

open Set Filter MeasureTheory

/-- Theorem 1, pp. 6–7. -/
theorem theorem_1
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
    (∀ t ∈ Ici t₀, 0 < wFun b β dβ t) ∧
    ((fun t => f (x t) - f xstar) =O[atTop] (fun t => 1 / (t ^ 2 * wFun b β dβ t))) ∧
    IntegrableOn (fun t => t ^ 2 * β t * wFun b β dβ t * ‖gradient f (x t)‖ ^ 2) (Ici t₀) ∧
    IntegrableOn
      (fun t => t * ((α - 3) * wFun b β dβ t - t * dw t) * (f (x t) - f xstar)) (Ici t₀) := by sorry

end HessianDamping.DINAVD
