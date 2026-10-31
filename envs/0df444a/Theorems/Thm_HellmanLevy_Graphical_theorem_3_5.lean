-- Prove2me | Theorems.Thm_HellmanLevy_Graphical_theorem_3_5
-- name    : HellmanLevy.Graphical.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:56:43.743984+00:00
-- url     : https://prove2.me/theorems/3acaa3d1-011b-413b-9f95-e31c4f3473f2
-- title:
--   Theorem 3.5 — a smooth graphical game admits a measurable Nash equilibrium (cited from Hellman–Levy 2019)
-- statement:
--   Let $(X,G,u)$ be a graphical game of countable degree on a standard Borel space $X$ with finite non-empty action set $A$, and suppose $G$ is a smooth graph. Then the game has a **measurable Nash equilibrium**: a Borel strategy profile $\sigma:X\to\Delta(A)$ such that for every vertex $g$ and every action $b\in A$
--   $$u(g,\sigma)\ge u(g,(b,(\sigma(h))_{h\ne g})).$$
--
--   The paper does not prove this theorem; it cites [Hellman and Levy, 2019]. It is used in the proof of Proposition 4.10, for a game whose components are finite.
--
--   Differences from the source:
--   - generalization: the vertex set of a graphical game is a Polish space → the vertex set X is a standard Borel space; reason: every Polish space is standard Borel and no notion used depends on the topology of X; the associated game of §4.2 lives on the type space, which is standard Borel without a named Polish topology
--   - encoding: payoff u : Ω × A^Ω → ℝ continuous in the Tychonoff topology on A × A^N(g), extended multilinearly to mixed profiles → u : X → (X → A) → ℝ with each u g continuous on A^X (A discrete) and depending only on g and N(g); the mixed payoff is the integral against the product measure ⊗_h σ(h); reason: given locality, continuity on A^X is continuity on A × A^N(g); the expectation under the product measure is the multilinear extension
--   - encoding: mixed actions in ∆(A) → probability mass functions PMF A; Borel strategies are those with every coordinate g ↦ σ(g)(b) measurable; reason: A is finite, so ∆(A) is the set of probability mass functions on A
--   - encoding: smooth: a Borel ψ into some Polish space Z with x E y ⟺ ψ(x) = ψ(y) (Definition 2.1) → a measurable ψ : X → ℝ with the same property; reason: every Polish space is Borel isomorphic to a Borel subset of ℝ; the paper's §6.1 states smoothness as E ≤_B id_ℝ
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), Theorem 3.5, p.15

import Mathlib
import Definitions.Def_HellmanLevy_Graphical_IsGraphicalGame
import Definitions.Def_HellmanLevy_Graphical_IsSmoothGraph
import Definitions.Def_HellmanLevy_Graphical_IsNashG

namespace HellmanLevy.Graphical

/-- **Theorem 3.5 (cited from Hellman–Levy 2019).** A smooth graphical game admits a measurable
Nash equilibrium: if `(X, G, u)` is a graphical game of countable degree on a standard Borel
space whose graph is smooth, there is a Borel strategy profile `σ : X → ∆(A)` from which no
vertex gains by deviating to a pure action.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), Theorem 3.5, p.15 ("The following theorem is proved in [Hellman and Levy, 2019]"; not
proved in this paper). The proof of Proposition 4.10 applies it to a game with finite classes. -/
theorem theorem_3_5 {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] {A : Type*}
    [Fintype A] [Nonempty A] [MeasurableSpace A] [DiscreteMeasurableSpace A]
    [TopologicalSpace A] [DiscreteTopology A] (G : X → X → Prop) (u : X → (X → A) → ℝ)
    (hG : IsSmoothGraph G) (hu : IsGraphicalGame G u) : ∃ σ : X → PMF A, IsNashG u σ := by sorry

end HellmanLevy.Graphical
