-- Prove2me | Theorems.Thm_HessianDamping_DINSC_theorem_7_beta_zero
-- name    : HessianDamping.DINSC.theorem_7_beta_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:57.04728+00:00
-- url     : https://prove2.me/theorems/34c11465-97b5-4c29-8d1f-f6e30f933aa8
-- title:
--   Theorem 7, last sentence, p. 19 — when β = 0, f(x(t)) − min f = O(e^{−√μ t}) as t → +∞
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $f:\mathcal H\to\mathbb R$ convex of class $\mathcal C^2$ and $\mu$-strongly convex for some $\mu>0$, with minimizer $x^\star$, and let $t_0>0$. Let $x:[t_0,+\infty[\to\mathcal H$ be a solution of the heavy ball equation with friction $2\sqrt\mu$,
--   $$\ddot x(t)+2\sqrt{\mu}\,\dot x(t)+\nabla f(x(t))=0,$$
--   that is, (19) with $\beta=0$. Then
--   $$f(x(t))-\min_{\mathcal H}f=\mathcal O\big(e^{-\sqrt\mu\,t}\big)\qquad\text{as }t\to+\infty .$$
--
--   The rate is twice the exponent of Theorem 7 (i). The paper states this in Theorem 7 without proof; Remark 7 attributes it to Siegel [29, Theorem 2.2].
--
--   **Formalization Note.** $\mathcal O$ is Landau's big-O along $t\to+\infty$; its constant may depend on $f$, $\mu$, $t_0$ and the trajectory.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 19, Theorem 7, last sentence ('When β = 0, …'); Remark 7

import Mathlib
import Definitions.Def_HessianDamping_DINSC_Setting

namespace HessianDamping.DINSC

open Set

/-- Theorem 7, last sentence, p. 19: when `β = 0`,
`f(x(t)) − min f = O(e^{−√μ t})` as `t → +∞`. -/
theorem theorem_7_beta_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC2 : ContDiff ℝ 2 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (x xd xdd : ℝ → H) (hx : IsSolution19 f μ 0 t₀ x xd xdd) :
    (fun t : ℝ => f (x t) - f xstar) =O[Filter.atTop] (fun t : ℝ => Real.exp (-(Real.sqrt μ) * t)) := by sorry

end HessianDamping.DINSC
