-- Prove2me | Theorems.Thm_NAGFlow_Flow_wellposed_56
-- name    : NAGFlow.Flow.wellposed_56
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:25.805252+00:00
-- url     : https://prove2.me/theorems/d0c3431d-5a0f-4250-96ca-b8ca679c5869
-- title:
--   Proof of Lemma 3.2, p. 13 — for f ∈ S^{1,1}_{μ,L} the system (56) has a unique classical solution (x, v) ∈ C¹([0, ∞); V)²
-- statement:
--   Let $V$ be a real Hilbert space, $f\in\mathcal S^{1,1}_{\mu,L}$ (so $\nabla f$ is $L$-Lipschitz), $\gamma_0>0$ and $\gamma(t)=\mu+(\gamma_0-\mu)e^{-t}$. For any $x_0,v_0\in V$ the system (56)
--   $$x'=v-x,\qquad \gamma v'=\mu(x-v)-\nabla f(x),\qquad x(0)=x_0,\ v(0)=v_0,$$
--   admits a classical solution $(x,v)\in C^1([0,\infty);V)\times C^1([0,\infty);V)$, and it is unique: any other classical solution coincides with it on $[0,\infty)$.
--
--   This is the well-posedness half of Lemma 3.2. It holds for $\mu=0$ as well, where $\gamma(t)=\gamma_0e^{-t}$ tends to $0$ but stays positive on every bounded interval.
--
--   **Formalization Note.** Uniqueness is equality on $[0,\infty)$, since values of the curves at negative times are not constrained. The derivatives are one-sided at $t=0$.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Lemma 3.2, first sentence, p. 13

import Mathlib
import Definitions.Def_NAGFlow_Flow_Setting

namespace NAGFlow.Flow

open Set

/-- Proof of Lemma 3.2, first sentence, p. 13. If `f ∈ S^{1,1}_{μ,L}` (so `∇f` is Lipschitz), `γ₀ > 0`
and `γ(t) = μ + (γ₀ − μ)e^{−t}`, then for any `x₀, v₀ ∈ V` the system (56) `x′ = v − x`,
`γ v′ = μ(x − v) − ∇f(x)`, `x(0) = x₀`, `v(0) = v₀` admits a classical solution
`(x, v) ∈ C¹([0, ∞); V) × C¹([0, ∞); V)`, and it is unique: any other classical solution agrees with
it on `[0, ∞)`. -/
theorem wellposed_56 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L γ₀ : ℝ) (hf : NAGFlow.PredCorr.IsS11 f gradf μ L) (hγ₀ : 0 < γ₀)
    (x₀ v₀ : V) :
    ∃ x v : ℝ → V, IsSys56 f gradf μ (gammaFn μ γ₀) x₀ v₀ x v ∧
      ∀ y w : ℝ → V, IsSys56 f gradf μ (gammaFn μ γ₀) x₀ v₀ y w →
        EqOn y x (Ici 0) ∧ EqOn w v (Ici 0) := by sorry

end NAGFlow.Flow
