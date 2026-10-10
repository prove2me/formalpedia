-- Prove2me | Theorems.Thm_NAGFlow_Flow_eq_59
-- name    : NAGFlow.Flow.eq_59
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:49.097985+00:00
-- url     : https://prove2.me/theorems/ff156bf8-2866-4ed3-b511-2654f0b529fd
-- title:
--   (59) along a solution of (56), p. 14 — μ/2‖y − x*‖² − ⟨∇f(y), y − x*⟩ ≤ f(x*) − f(y) and ℒ′(t) ≤ −ℒ(t) − μ/2‖x′(t)‖²
-- statement:
--   Let $V$ be a real Hilbert space, $f\in\mathcal S^1_\mu$, $\gamma_0>0$, $\gamma(t)=\mu+(\gamma_0-\mu)e^{-t}$, $x^*$ a global minimizer of $f$, and $(x,v)\in C^1([0,\infty);V)^2$ a classical solution of (56). Then:
--   1. by the $\mu$-convexity (2), for every $y\in V$
--   $$\frac{\mu}{2}\|y-x^*\|^2-\langle\nabla f(y),y-x^*\rangle\le f(x^*)-f(y);$$
--   2. the Lyapunov function $\mathcal L(t)=f(x(t))-f(x^*)+\frac{\gamma(t)}{2}\|v(t)-x^*\|^2$ is differentiable on $[0,\infty)$ (right derivative at $0$) and
--   $$\mathcal L'(t)\le-\mathcal L(t)-\frac{\mu}{2}\|x'(t)\|^2\qquad\forall\,t\ge0. \tag{59}$$
--
--   This is the differential inequality of Lemma 3.2, proved for every classical solution of (56) and with only $\mu$-convexity of $f$; Lipschitz continuity of $\nabla f$ is used in Lemma 3.2 only for existence.
--
--   **Formalization Note.** "$\mathcal L'(t)\le\dots$" is stated as: there is a number $d$ with `HasDerivWithinAt ℒ d (Ici 0) t` and $d\le-\mathcal L(t)-\frac{\mu}{2}\|x'(t)\|^2$. The page says "$f$ is $\mu$-strongly convex"; the inequality uses only (2), which allows $\mu=0$.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Lemma 3.2, last three displays, p. 14

import Mathlib
import Definitions.Def_NAGFlow_Flow_Setting

namespace NAGFlow.Flow

open Set
open scoped InnerProductSpace

/-- Proof of Lemma 3.2, last part, p. 14: (59) along any solution of (56). Let `f ∈ S¹_μ`, `γ₀ > 0`,
`γ(t) = μ + (γ₀ − μ)e^{−t}`, `x*` a global minimizer, `(x, v)` a classical `C¹` solution of (56).
By μ-convexity (2), `μ/2 ‖y − x*‖² − ⟨∇f(y), y − x*⟩ ≤ f(x*) − f(y)` for every `y`, and the
Lyapunov function (58) is differentiable on `[0, ∞)` (right derivative at `0`) with
`ℒ′(t) ≤ −ℒ(t) − μ/2 ‖x′(t)‖²` for every `t ≥ 0`. -/
theorem eq_59 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ γ₀ : ℝ) (hf : NAGFlow.PredCorr.IsS1 f gradf μ) (hγ₀ : 0 < γ₀)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y) (x₀ v₀ : V) (x v : ℝ → V)
    (hsol : IsSys56 f gradf μ (gammaFn μ γ₀) x₀ v₀ x v) :
    (∀ y : V, μ / 2 * ‖y - xstar‖ ^ 2 - ⟪gradf y, y - xstar⟫_ℝ ≤ f xstar - f y) ∧
    ∀ t : ℝ, 0 ≤ t → ∃ dL : ℝ,
      HasDerivWithinAt (lyapFlow f xstar (gammaFn μ γ₀) x v) dL (Ici 0) t ∧
      dL ≤ -lyapFlow f xstar (gammaFn μ γ₀) x v t - μ / 2 * ‖dI x t‖ ^ 2 := by sorry

end NAGFlow.Flow
