-- Prove2me | Theorems.Thm_NAGFlow_Flow_lemma_3_2
-- name    : NAGFlow.Flow.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:56.470587+00:00
-- url     : https://prove2.me/theorems/166c5b2c-639d-49fc-bdef-1dd57a2d409a
-- title:
--   Lemma 3.2, p. 13 — for f ∈ S^{1,1}_{μ,L} the NAG flow (57) has a unique C² solution, ℒ′ ≤ −ℒ − μ/2‖x′‖² (59), and (60)
-- statement:
--   Let $V$ be a real Hilbert space and $f\in\mathcal S^{1,1}_{\mu,L}$ with $\mu\ge0$: $f$ is continuously differentiable, $\mu$-convex,
--   $$f(x)-f(y)-\langle\nabla f(y),x-y\rangle\ge\frac{\mu}{2}\|x-y\|^2,$$
--   and $\nabla f$ is $L$-Lipschitz with $0<L<\infty$. Let $x^*$ be a global minimizer of $f$, $\gamma_0>0$, $\gamma(t)=\mu+(\gamma_0-\mu)e^{-t}$ the solution of (54) $\gamma'=\mu-\gamma$, $\gamma(0)=\gamma_0$, and $x_0,v_0\in V$.
--
--   Then the NAG flow
--   $$\gamma x''+(\mu+\gamma)x'+\nabla f(x)=0,\qquad x(0)=x_0,\ x'(0)=v_0-x_0, \tag{57}$$
--   admits a unique solution $x\in C^2([0,\infty);V)$. Moreover, with $v=x+x'$ and the Lyapunov function
--   $$\mathcal L(t)=f(x(t))-f(x^*)+\frac{\gamma(t)}{2}\|v(t)-x^*\|^2, \tag{58}$$
--   $\mathcal L$ is differentiable on $[0,\infty)$ and
--   $$\mathcal L'(t)\le-\mathcal L(t)-\frac{\mu}{2}\|x'(t)\|^2, \tag{59}$$
--   which implies
--   $$\mathcal L(t)+\frac{\mu}{2}\int_0^te^{s-t}\|x'(s)\|^2\,ds\le e^{-t}\mathcal L(0),\qquad t\ge0. \tag{60}$$
--
--   The lemma is the continuous model behind the accelerated methods of the paper: the NAG flow decays the Lyapunov function at the rate $e^{-t}$ for every $\mu\ge0$, and the discrete schemes are designed so that one step contracts $\mathcal L_k$ by a factor $1/(1+\alpha_k)$, the discrete analogue of $e^{-t}$.
--
--   **Formalization Note.** $V$ is a real Hilbert space; the duality pairing is the inner product (Riesz). Uniqueness is equality on $[0,\infty)$, because a function $\mathbb R\to V$ is unconstrained at negative times. Derivatives are relative to $[0,\infty)$, so one-sided at $t=0$; "$\mathcal L'(t)\le\dots$" means that $\mathcal L$ has a one-sided derivative $d$ at $t$ with $d\le-\mathcal L(t)-\frac{\mu}{2}\|x'(t)\|^2$. The integral in (60) is an interval integral of a continuous integrand (the solution is $C^2$), so no junk value for non-integrable functions enters. The hypothesis that $x^*$ is a minimizer is the paper's standing assumption that $\operatorname{argmin}f$ is nonempty.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, Lemma 3.2 and Eqs. (59)–(60), p. 13

import Mathlib
import Definitions.Def_NAGFlow_Flow_Setting

namespace NAGFlow.Flow

open Set

/-- Lemma 3.2, p. 13. Let `f ∈ S^{1,1}_{μ,L}` with `μ ≥ 0`, `γ₀ > 0`, `γ(t) = μ + (γ₀ − μ)e^{−t}`
(the solution of (54)), `x₀, v₀ ∈ V`, and `x*` a global minimizer of `f`. Then the NAG flow (57)
`γx″ + (μ + γ)x′ + ∇f(x) = 0`, `x(0) = x₀`, `x′(0) = v₀ − x₀`, admits a solution
`x ∈ C²([0, ∞); V)`, unique on `[0, ∞)`; and, with `v = x + x′` and the Lyapunov function (58)
`ℒ(t) = f(x(t)) − f(x*) + γ(t)/2 ‖v(t) − x*‖²`, `ℒ` is differentiable on `[0, ∞)` (right derivative
at `0`) with
`ℒ′(t) ≤ −ℒ(t) − μ/2 ‖x′(t)‖²` (59), and
`ℒ(t) + μ/2 ∫₀ᵗ e^{s−t} ‖x′(s)‖² ds ≤ e^{−t} ℒ(0)` for all `t ≥ 0` (60). -/
theorem lemma_3_2 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L γ₀ : ℝ) (hf : NAGFlow.PredCorr.IsS11 f gradf μ L) (hγ₀ : 0 < γ₀)
    (x₀ v₀ xstar : V) (hxstar : ∀ y, f xstar ≤ f y) :
    ∃ x : ℝ → V, IsNAGSolution2 f gradf μ γ₀ x₀ v₀ x ∧
      (∀ y : ℝ → V, IsNAGSolution2 f gradf μ γ₀ x₀ v₀ y → EqOn y x (Ici 0)) ∧
      (∀ t : ℝ, 0 ≤ t → ∃ dL : ℝ,
        HasDerivWithinAt (lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s)) dL
          (Ici 0) t ∧
        dL ≤ -lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s) t
          - μ / 2 * ‖dI x t‖ ^ 2) ∧
      (∀ t : ℝ, 0 ≤ t →
        lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s) t
          + μ / 2 * ∫ s in (0 : ℝ)..t, Real.exp (s - t) * ‖dI x s‖ ^ 2
        ≤ Real.exp (-t) * lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s) 0) := by sorry

end NAGFlow.Flow
