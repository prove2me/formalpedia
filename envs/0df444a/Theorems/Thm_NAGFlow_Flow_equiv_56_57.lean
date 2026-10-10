-- Prove2me | Theorems.Thm_NAGFlow_Flow_equiv_56_57
-- name    : NAGFlow.Flow.equiv_56_57
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:26.76845+00:00
-- url     : https://prove2.me/theorems/f9976ca4-8a57-4c13-ae23-4e14663df8c5
-- title:
--   p. 13 — a C¹ solution (x, v) of (56) gives a C² solution x of (57), and a C² solution x of (57) gives the solution (x, x + x′) of (56)
-- statement:
--   Let $V$ be a real Hilbert space, $f\in\mathcal S^1_\mu$, $\gamma_0>0$, $\gamma(t)=\mu+(\gamma_0-\mu)e^{-t}$, and $x_0,v_0\in V$.
--   1. If $(x,v)\in C^1([0,\infty);V)^2$ solves (56) $x'=v-x$, $\gamma v'=\mu(x-v)-\nabla f(x)$ with $x(0)=x_0$, $v(0)=v_0$, then $x'=v-x\in C^1([0,\infty);V)$, hence $x\in C^2([0,\infty);V)$, and $x$ solves the NAG flow
--   $$\gamma x''+(\mu+\gamma)x'+\nabla f(x)=0,\qquad x(0)=x_0,\ x'(0)=v_0-x_0. \tag{57}$$
--   2. Conversely, if $x\in C^2([0,\infty);V)$ solves (57) with these initial conditions, then $(x,\,x+x')$ is a classical solution of (56) with $x(0)=x_0$, $v(0)=v_0$.
--
--   Together with the well-posedness of (56), this shows that (57) has exactly one solution in $C^2([0,\infty);V)$, as stated in Lemma 3.2.
--
--   **Formalization Note.** The paper asserts the equivalence of (56) and (57) on p. 13 and uses direction 1 in the proof of Lemma 3.2; direction 2 is the half of "equivalent" that turns uniqueness for (56) into uniqueness for (57). Only $\mathcal S^1_\mu$ is assumed: Lipschitz continuity of $\nabla f$ is not needed for this step.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, p. 13: sentence introducing (57) and proof of Lemma 3.2, second and third sentences

import Mathlib
import Definitions.Def_NAGFlow_Flow_Setting

namespace NAGFlow.Flow

open Set

/-- Proof of Lemma 3.2, last two sentences of its first paragraph, p. 13, together with the
equivalence of (56) and (57) asserted on p. 13. Let `f ∈ S¹_μ`, `γ₀ > 0` and
`γ(t) = μ + (γ₀ − μ)e^{−t}`.
1. If `(x, v)` is a classical `C¹` solution of (56) with `x(0) = x₀`, `v(0) = v₀`, then
   `x′ = v − x ∈ C¹([0, ∞); V)`, so `x ∈ C²([0, ∞); V)`, and `x` solves the NAG flow (57)
   with `x(0) = x₀`, `x′(0) = v₀ − x₀`.
2. Conversely, if `x ∈ C²([0, ∞); V)` solves (57) with these initial conditions, then
   `(x, x + x′)` is a classical solution of (56) with `x(0) = x₀`, `v(0) = v₀`. -/
theorem equiv_56_57 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ γ₀ : ℝ) (hf : NAGFlow.PredCorr.IsS1 f gradf μ) (hγ₀ : 0 < γ₀)
    (x₀ v₀ : V) :
    (∀ x v : ℝ → V, IsSys56 f gradf μ (gammaFn μ γ₀) x₀ v₀ x v →
      IsNAGSolution2 f gradf μ γ₀ x₀ v₀ x) ∧
    (∀ x : ℝ → V, IsNAGSolution2 f gradf μ γ₀ x₀ v₀ x →
      IsSys56 f gradf μ (gammaFn μ γ₀) x₀ v₀ x (fun t => x t + dI x t)) := by sorry

end NAGFlow.Flow
