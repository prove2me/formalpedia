-- Prove2me | Theorems.Thm_HessianDamping_DINSC_theorem_7
-- name    : HessianDamping.DINSC.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:57.684988+00:00
-- url     : https://prove2.me/theorems/5e9e1edf-05fc-43f6-92a0-4aff60618080
-- title:
--   Theorem 7, p. 19 — for μ-strongly convex f and 0 ≤ β ≤ 1/(2√μ), (DIN)_{2√μ,β} trajectories satisfy f(x(t)) − min f ≤ Ce^{−(√μ/2)(t−t₀)}
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $f:\mathcal H\to\mathbb R$ a convex function of class $\mathcal C^2$ which is $\mu$-strongly convex for some $\mu>0$ (that is, $f-\frac\mu2\|\cdot\|^2$ is convex), and let $x^\star$ be its minimizer. Let $t_0>0$ and $0\le\beta\le\frac{1}{2\sqrt\mu}$, and let $x:[t_0,+\infty[\to\mathcal H$ be a solution trajectory of
--   $$\ddot x(t)+2\sqrt{\mu}\,\dot x(t)+\beta\nabla^2 f(x(t))\dot x(t)+\nabla f(x(t))=0. \tag{19}$$
--   Then:
--
--   1. for all $t\ge t_0$,
--   $$\frac\mu2\|x(t)-x^\star\|^2\le f(x(t))-\min_{\mathcal H}f\le C\,e^{-\frac{\sqrt\mu}{2}(t-t_0)},$$
--   where $C:=f(x(t_0))-\min_{\mathcal H}f+\mu\|x(t_0)-x^\star\|^2+\|\dot x(t_0)+\beta\nabla f(x(t_0))\|^2$;
--   2. there is a constant $C_1>0$ such that, for all $t\ge t_0$,
--   $$e^{-\sqrt\mu\,t}\int_{t_0}^{t}e^{\sqrt\mu\,s}\|\nabla f(x(s))\|^2\,ds\le C_1\,e^{-\frac{\sqrt\mu}{2}t};$$
--   3. moreover,
--   $$\int_{t_0}^{\infty}e^{\frac{\sqrt\mu}{2}t}\|\dot x(t)\|^2\,dt<+\infty .$$
--
--   The theorem gives exponential decay of the values, of the distance to the minimizer and, in an averaged sense, of the gradients, for the inertial dynamic with viscous damping $2\sqrt\mu$ and Hessian-driven damping $\beta$. It is the continuous-time model behind the algorithms (IPAHD-SC) and (IGAHD-SC) of §5.
--
--   **Formalization Note.** A trajectory is a triple of maps $x,\dot x,\ddot x:\mathbb R\to\mathcal H$ whose derivatives are taken within $[t_0,+\infty[$ (one-sided at $t_0$); values before $t_0$ are irrelevant, and $\dot x(t_0)$ in $C$ is the right derivative. $\min_{\mathcal H}f$ is written $f(x^\star)$ for a point $x^\star$ with $f(x^\star)\le f(y)$ for all $y$ (the standing hypothesis $\operatorname{argmin}f\neq\emptyset$). The integral in item 2 is an interval integral of a function continuous on $[t_0,t]$, and item 3 is stated as integrability of the nonnegative integrand on $[t_0,+\infty[$. The constant $C_1$ may depend on all data, including the trajectory. The last sentence of the paper's Theorem 7 (the case $\beta=0$) is a separate item. Convexity of $f$ is kept from the standing hypothesis (H) although strong convexity implies it.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 19, Theorem 7 (i), (ii) and 'Moreover'; standing hypothesis (H), p. 2

import Mathlib
import Definitions.Def_HessianDamping_DINSC_Setting

namespace HessianDamping.DINSC

open Set

/-- Theorem 7, p. 19: for `μ`-strongly convex `f` and `0 ≤ β ≤ 1/(2√μ)`, every solution of (19)
satisfies (i) `(μ/2)‖x(t) − x⋆‖² ≤ f(x(t)) − min f ≤ C e^{−(√μ/2)(t − t₀)}` with
`C = f(x(t₀)) − min f + μ‖x(t₀) − x⋆‖² + ‖ẋ(t₀) + β∇f(x(t₀))‖²`; (ii) the weighted gradient
average bound; and `∫_{t₀}^∞ e^{(√μ/2)t}‖ẋ(t)‖² dt < +∞`. -/
theorem theorem_7 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC2 : ContDiff ℝ 2 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (x xd xdd : ℝ → H) (hx : IsSolution19 f μ β t₀ x xd xdd) :
    (∀ t ∈ Ici t₀, μ / 2 * ‖x t - xstar‖ ^ 2 ≤ f (x t) - f xstar ∧
      f (x t) - f xstar ≤
        (f (x t₀) - f xstar + μ * ‖x t₀ - xstar‖ ^ 2 + ‖xd t₀ + β • gradient f (x t₀)‖ ^ 2)
          * Real.exp (-(Real.sqrt μ / 2) * (t - t₀))) ∧
    (∃ C₁ : ℝ, 0 < C₁ ∧ ∀ t ∈ Ici t₀,
      Real.exp (-(Real.sqrt μ) * t) *
          ∫ s in t₀..t, Real.exp (Real.sqrt μ * s) * ‖gradient f (x s)‖ ^ 2
        ≤ C₁ * Real.exp (-(Real.sqrt μ / 2) * t)) ∧
    MeasureTheory.IntegrableOn (fun t => Real.exp (Real.sqrt μ / 2 * t) * ‖xd t‖ ^ 2) (Ici t₀) := by sorry

end HessianDamping.DINSC
