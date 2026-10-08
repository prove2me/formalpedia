-- Prove2me | Theorems.Thm_HessianDamping_DINSC_lyap_le_exp
-- name    : HessianDamping.DINSC.lyap_le_exp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:13.43118+00:00
-- url     : https://prove2.me/theorems/1da48df7-c2e3-4265-96b1-a1b891ad19d3
-- title:
--   Proof of Theorem 7, p. 21 — E(t) ≤ E(t₀)e^{−(√μ/2)(t−t₀)} for t ≥ t₀
-- statement:
--   Under the hypotheses of Theorem 7 — $\mathcal H$ a real Hilbert space, $f$ convex of class $\mathcal C^2$ and $\mu$-strongly convex ($\mu>0$) with minimizer $x^\star$, $t_0>0$, $0\le\beta\le\frac1{2\sqrt\mu}$, and $x$ a solution of
--   $$\ddot x(t)+2\sqrt{\mu}\,\dot x(t)+\beta\nabla^2 f(x(t))\dot x(t)+\nabla f(x(t))=0$$
--   on $[t_0,+\infty[$ — the Lyapunov function $\mathcal E(t)=f(x(t))-f(x^\star)+\frac12\|\sqrt{\mu}(x(t)-x^\star)+\dot x(t)+\beta\nabla f(x(t))\|^2$ satisfies, for all $t\ge t_0$,
--   $$\mathcal E(t)\le\mathcal E(t_0)\,e^{-\frac{\sqrt\mu}{2}(t-t_0)} .$$
--
--   Since $\mathcal E(t)\ge f(x(t))-\min f$, this gives the exponential decay of the values in Theorem 7 (i).
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 21, §4.1, proof of Theorem 7 (i), display after 'By integrating the differential inequality above we obtain'

import Mathlib
import Definitions.Def_HessianDamping_DINSC_Setting

namespace HessianDamping.DINSC

open Set

/-- Proof of Theorem 7, p. 21: `E(t) ≤ E(t₀) e^{−(√μ/2)(t − t₀)}` for all `t ≥ t₀`. -/
theorem lyap_le_exp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC2 : ContDiff ℝ 2 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (x xd xdd : ℝ → H) (hx : IsSolution19 f μ β t₀ x xd xdd) :
    ∀ t ∈ Ici t₀, lyap f μ β xstar x xd t ≤
      lyap f μ β xstar x xd t₀ * Real.exp (-(Real.sqrt μ / 2) * (t - t₀)) := by sorry

end HessianDamping.DINSC
