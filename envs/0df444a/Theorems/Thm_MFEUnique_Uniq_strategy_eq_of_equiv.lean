-- Prove2me | Theorems.Thm_MFEUnique_Uniq_strategy_eq_of_equiv
-- name    : MFEUnique.Uniq.strategy_eq_of_equiv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:09.873388+00:00
-- url     : https://prove2.me/theorems/7df3699f-e8e9-40e3-a0c8-b7b84f767e84
-- title:
--   p. 13, proof of Theorem 1 — s₁ ∼ s₂ implies g(x, s₁) = g(x, s₂) for all x ∈ X
-- statement:
--   Consider the game under the standing assumptions, with $G$ single-valued and $g$ its selection, and let $\succeq$ be a binary relation on $\mathcal P(X)$ with the standing property of p. 12 (if $s_2 \sim s_1$ then $\pi(\cdot, \cdot, s_1) = \pi(\cdot, \cdot, s_2)$ and $w(\cdot, \cdot, s_1, \cdot) = w(\cdot, \cdot, s_2, \cdot)$). If $s_1 \succeq s_2$ and $s_2 \succeq s_1$, then the players play the same strategy under $s_1$ as under $s_2$:
--   $$g(x, s_1) = g(x, s_2) \quad \text{for all } x \in X.$$
--
--   The content is that the value function $V(\cdot, s)$, and with it the optimal correspondence $G(\cdot, s)$, depend on the population state only through $\pi(\cdot, \cdot, s)$ and $w(\cdot, \cdot, s, \cdot)$. It is the step that turns equivalence under $\succeq$ into equality of the kernels $Q(\cdot, s_1, \cdot) = Q(\cdot, s_2, \cdot)$.
-- source:
--   Light and Weintraub, Mean Field Equilibrium: Uniqueness, Existence, and Comparative Statics, arXiv:1903.02273v3, p. 13, proof of Theorem 1, third paragraph

import Mathlib
import Definitions.Def_MFEUnique_Uniq_Equilibrium

open MeasureTheory

namespace MFEUnique.Uniq

/-- p. 13, proof of Theorem 1: if `s₁ ∼ s₂` (i.e. `s₁ ⪰ s₂` and `s₂ ⪰ s₁`), then the payoff and
transition functions agree under `s₁` and `s₂`, so the players play the same strategy:
`g(x, s₁) = g(x, s₂)` for all `x ∈ X`. -/
theorem strategy_eq_of_equiv {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X]
    {q J : ℕ} {A : Set (EuclideanSpace ℝ (Fin q))} {E : Type*} [TopologicalSpace E]
    (G : Game X q J E A) (hG : G.Standing)
    (R : ProbabilityMeasure X → ProbabilityMeasure X → Prop) (hR : G.RelStanding R)
    (g : X → ProbabilityMeasure X → A) (hg : ∀ x s, g x s ∈ G.Gopt x s)
    (hsingle : ∀ x s a, a ∈ G.Gopt x s → a = g x s)
    (s₁ s₂ : ProbabilityMeasure X) (h₁₂ : R s₁ s₂) (h₂₁ : R s₂ s₁) :
    ∀ x : X, g x s₁ = g x s₂ := by sorry

end MFEUnique.Uniq
