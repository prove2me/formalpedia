-- Prove2me | Theorems.Thm_HellmanLevy_Graphical_lemma_4_8
-- name    : HellmanLevy.Graphical.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:56:36.564989+00:00
-- url     : https://prove2.me/theorems/8ad39c43-01bd-4618-b930-279d2dfeb199
-- title:
--   Lemma 4.8 — approximation by payoffs depending on finitely many neighbours (corrected: a finite-section $D\subseteq G$ instead of a finite-degree graph)
-- statement:
--   Let $(X,G,u)$ be a graphical game of countable degree on a standard Borel space and let $\varepsilon>0$. Then there are a payoff $u'$ and a Borel relation $D\subseteq G$ in which every vertex has finitely many $D$-neighbours such that
--
--   1. $(X,G,u')$ is a graphical game;
--   2. each $u'(g,\cdot)$ depends only on the actions of $g$ and of its $D$-neighbours;
--   3. $|u(g,a)-u'(g,a)|\le\varepsilon$ for every vertex $g$ and every pure profile $a$; in particular $(X,G,u')$ is $\varepsilon$-close to $(X,G,u)$ (Definition 4.7) for every measure $\mu$ on $X$.
--
--   Truncating each player's dependence to finitely many neighbours is what makes Propositions 4.9 and 4.10 applicable to games of countable degree.
--
--   Differences from the source:
--   - correction: a graphical game Γ′ = (Ω, G′, u′) with G′ ⊆ G and each node of G′ of finite degree → a Borel D ⊆ G with finite sections D_g, (X, G, u′) a graphical game and u′ depending only on D; reason: the printed lemma is false because a graph is symmetric: on X = ℕ with the star G = {(0, n), (n, 0) | n ≥ 1}, A = {0, 1}, u(n, a) = 1[a(n) = a(0)] for n ≥ 1, u(0, ·) = 0, µ = Σ 2^(−n−1) δₙ, ε = 1/4, every edge (n, 0) must lie in G′, so 0 has infinite G′-degree; the paper's own G′ (p.24) is not symmetric and has finite out-degree, which D is
--   - generalization: ε-close: |u − u′| ≤ ε outside a µ-null set, for a given measure µ → |u(g, a) − u′(g, a)| ≤ ε for every vertex g and profile a; reason: a stronger conclusion that implies ε-closeness for every µ (the paper's construction gives it everywhere), so µ is not a parameter
--   - generalization: the vertex set of a graphical game is a Polish space → the vertex set X is a standard Borel space; reason: every Polish space is standard Borel and no notion used depends on the topology of X; the associated game of §4.2 lives on the type space, which is standard Borel without a named Polish topology
--   - encoding: payoff u : Ω × A^Ω → ℝ continuous in the Tychonoff topology on A × A^N(g), extended multilinearly to mixed profiles → u : X → (X → A) → ℝ with each u g continuous on A^X (A discrete) and depending only on g and N(g); the mixed payoff is the integral against the product measure ⊗_h σ(h); reason: given locality, continuity on A^X is continuity on A × A^N(g); the expectation under the product measure is the multilinear extension
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), Lemma 4.8, p.22; Definition 4.7, p.22; construction of G′ and u′, p.24

import Mathlib
import Definitions.Def_HellmanLevy_Graphical_IsGraphicalGame

namespace HellmanLevy.Graphical

/-- **Lemma 4.8 (corrected: finite-section dependency relation instead of a finite-degree
graph).** Let `(X, G, u)` be a graphical game and `ε > 0`. Then there are a payoff `u'` and a
Borel relation `D ⊆ G` in which every vertex has finitely many `D`-neighbours, such that
`(X, G, u')` is a graphical game, each payoff `u' g` depends only on `g`'s action and the actions
of its `D`-neighbours, and `|u(g, a) − u'(g, a)| ≤ ε` for every vertex `g` and every profile `a`
(so `u'` is ε-close to `u`, Definition 4.7, for every measure `µ`).
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), Lemma 4.8, p.22; Definition 4.7, p.22; construction of `G′` and `u′`, p.24.

**Formalization Note** As printed, the lemma asks for a graph `G′ ⊆ G` in which every node has
finite degree; since a graph is symmetric this is false (the star on `ℕ` with centre `0`,
`A = {0, 1}`, `u(n, a) = 1[a(n) = a(0)]` for `n ≥ 1`, `u(0, ·) = 0`, `µ = Σ 2^(−n−1) δₙ`, `ε = 1/4`
forces every edge `(n, 0)` into `G′`). The paper's own `G′ = {(ω, θ) | θ ≠ ω, θ = φⱼ(ω),
j ≤ N(ω)}` is not symmetric and has finite out-degree; `D` is that relation. -/
theorem lemma_4_8 {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] {A : Type*}
    [Fintype A] [Nonempty A] [MeasurableSpace A] [DiscreteMeasurableSpace A]
    [TopologicalSpace A] [DiscreteTopology A] (G : X → X → Prop) (u : X → (X → A) → ℝ) (hu : IsGraphicalGame G u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (u' : X → (X → A) → ℝ) (D : X → X → Prop), CBER.IsBorelRel D ∧ (∀ x y, D x y → G x y) ∧
      (∀ x, {y | D x y}.Finite) ∧ IsGraphicalGame G u' ∧ DependsOn u' D ∧
      ∀ g a, |u g a - u' g a| ≤ ε := by sorry

end HellmanLevy.Graphical
