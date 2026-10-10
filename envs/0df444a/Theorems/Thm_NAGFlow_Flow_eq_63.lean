-- Prove2me | Theorems.Thm_NAGFlow_Flow_eq_63
-- name    : NAGFlow.Flow.eq_63
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:39.912294+00:00
-- url     : https://prove2.me/theorems/30d13ee2-2bda-4f19-8203-762afa6acde5
-- title:
--   (63), p. 14 — along a solution of (56), ℒ′ = μ/2‖x − x*‖² − ⟨∇f(x), x − x*⟩ − γ/2‖v − x*‖² − μ/2‖x′‖²
-- statement:
--   Under the hypotheses of (61) — $V$ a real Hilbert space, $f\in\mathcal S^1_\mu$, $\gamma_0>0$, $\gamma(t)=\mu+(\gamma_0-\mu)e^{-t}$, $x^*$ a global minimizer of $f$, and $(x,v)\in C^1([0,\infty);V)^2$ a classical solution of (56) — the Lyapunov function $\mathcal L(t)=f(x)-f(x^*)+\frac{\gamma}{2}\|v-x^*\|^2$ satisfies, for every $t\ge0$,
--   $$\mathcal L'(t)=\frac{\mu}{2}\|x-x^*\|^2-\langle\nabla f(x),x-x^*\rangle-\frac{\gamma}{2}\|v-x^*\|^2-\frac{\mu}{2}\|x'\|^2, \tag{63}$$
--   with all functions evaluated at $t$ and the derivative one-sided at $t=0$.
--
--   The identity isolates the term $\frac{\mu}{2}\|x-x^*\|^2-\langle\nabla f(x),x-x^*\rangle$, which $\mu$-convexity bounds by $f(x^*)-f(x)$.
--
--   **Formalization Note.** Stated as `HasDerivWithinAt` on $[0,\infty)$; $x'$ is the one-sided derivative `dI x`.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Lemma 3.2, (62)–(63), p. 14

import Mathlib
import Definitions.Def_NAGFlow_Flow_Setting

namespace NAGFlow.Flow

open Set
open scoped InnerProductSpace

/-- Proof of Lemma 3.2, (63), p. 14. Under the hypotheses of (61) (`f ∈ S¹_μ`, `γ₀ > 0`,
`γ(t) = μ + (γ₀ − μ)e^{−t}`, `x*` a global minimizer, `(x, v)` a classical `C¹` solution of (56)),
the Lyapunov function (58) has, at every `t ≥ 0` (right derivative at `0`),
`ℒ′(t) = μ/2 ‖x − x*‖² − ⟨∇f(x), x − x*⟩ − γ/2 ‖v − x*‖² − μ/2 ‖x′‖²`. -/
theorem eq_63 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ γ₀ : ℝ) (hf : NAGFlow.PredCorr.IsS1 f gradf μ) (hγ₀ : 0 < γ₀)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y) (x₀ v₀ : V) (x v : ℝ → V)
    (hsol : IsSys56 f gradf μ (gammaFn μ γ₀) x₀ v₀ x v) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (lyapFlow f xstar (gammaFn μ γ₀) x v)
      (μ / 2 * ‖x t - xstar‖ ^ 2 - ⟪gradf (x t), x t - xstar⟫_ℝ
        - gammaFn μ γ₀ t / 2 * ‖v t - xstar‖ ^ 2 - μ / 2 * ‖dI x t‖ ^ 2) (Ici 0) t := by sorry

end NAGFlow.Flow
