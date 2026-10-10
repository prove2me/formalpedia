-- Prove2me | Theorems.Thm_NAGFlow_Flow_eq_61
-- name    : NAGFlow.Flow.eq_61
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:17.533662+00:00
-- url     : https://prove2.me/theorems/79b04830-3632-4191-89c3-5d9e657fed0f
-- title:
--   (61), pp. 13–14 — along a solution of (56), ℒ′ = ⟨∇f(x), x′⟩ + (μ − γ)/2‖v − x*‖² + ⟨μ(x − v) − ∇f(x), v − x*⟩
-- statement:
--   Let $V$ be a real Hilbert space, $f\in\mathcal S^1_\mu$, $\gamma_0>0$, $\gamma(t)=\mu+(\gamma_0-\mu)e^{-t}$, $x^*$ a global minimizer of $f$, and $(x,v)\in C^1([0,\infty);V)^2$ a classical solution of (56). Let
--   $$\mathcal L(t)=f(x(t))-f(x^*)+\frac{\gamma(t)}{2}\|v(t)-x^*\|^2 .$$
--   Then for every $t\ge0$, $\mathcal L$ is differentiable at $t$ relative to $[0,\infty)$, and
--   $$\mathcal L'(t)=\langle\nabla f(x),x'\rangle+\frac{\gamma'}{2}\|v-x^*\|^2+\gamma\langle v',v-x^*\rangle,$$
--   which, after replacing $\gamma'$ and $v'$ by the right-hand sides of (54) and (56), equals
--   $$\mathcal L'(t)=\langle\nabla f(x),x'\rangle+\frac{\mu-\gamma}{2}\|v-x^*\|^2+\langle\mu(x-v)-\nabla f(x),v-x^*\rangle. \tag{61}$$
--   All functions are evaluated at $t$.
--
--   This is the first step of the Lyapunov analysis of the NAG flow.
--
--   **Formalization Note.** Both expressions are stated as one-sided derivatives (`HasDerivWithinAt` on $[0,\infty)$). $x'$, $v'$ and $\gamma'$ are the one-sided derivatives `dI`; since the curves are $C^1$ on $[0,\infty)$ these are the genuine derivatives. That $x^*$ is a minimizer is the paper's standing assumption; the identity itself does not use it.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Lemma 3.2, last display of p. 13 and (61), p. 14

import Mathlib
import Definitions.Def_NAGFlow_Flow_Setting

namespace NAGFlow.Flow

open Set
open scoped InnerProductSpace

/-- Proof of Lemma 3.2, the display before (61) (p. 13) and (61) (p. 14). Let `f ∈ S¹_μ`, `γ₀ > 0`,
`γ(t) = μ + (γ₀ − μ)e^{−t}`, `x*` a global minimizer of `f`, and `(x, v)` a classical `C¹` solution
of (56) on `[0, ∞)`. Then the Lyapunov function `ℒ(t) = f(x) − f(x*) + γ/2 ‖v − x*‖²` of (58) is
differentiable on `[0, ∞)` (right derivative at `0`) with
`ℒ′(t) = ⟨∇f(x), x′⟩ + γ′/2 ‖v − x*‖² + γ⟨v′, v − x*⟩`, and, replacing `γ′` and `v′` by the right
hand sides of (54) and (56),
`ℒ′(t) = ⟨∇f(x), x′⟩ + (μ − γ)/2 ‖v − x*‖² + ⟨μ(x − v) − ∇f(x), v − x*⟩` (61). -/
theorem eq_61 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ γ₀ : ℝ) (hf : NAGFlow.PredCorr.IsS1 f gradf μ) (hγ₀ : 0 < γ₀)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y) (x₀ v₀ : V) (x v : ℝ → V)
    (hsol : IsSys56 f gradf μ (gammaFn μ γ₀) x₀ v₀ x v) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (lyapFlow f xstar (gammaFn μ γ₀) x v)
      (⟪gradf (x t), dI x t⟫_ℝ + dI (gammaFn μ γ₀) t / 2 * ‖v t - xstar‖ ^ 2
        + gammaFn μ γ₀ t * ⟪dI v t, v t - xstar⟫_ℝ) (Ici 0) t ∧
    HasDerivWithinAt (lyapFlow f xstar (gammaFn μ γ₀) x v)
      (⟪gradf (x t), dI x t⟫_ℝ + (μ - gammaFn μ γ₀ t) / 2 * ‖v t - xstar‖ ^ 2
        + ⟪μ • (x t - v t) - gradf (x t), v t - xstar⟫_ℝ) (Ici 0) t := by sorry

end NAGFlow.Flow
