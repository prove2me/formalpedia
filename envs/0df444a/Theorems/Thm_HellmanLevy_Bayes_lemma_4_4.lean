-- Prove2me | Theorems.Thm_HellmanLevy_Bayes_lemma_4_4
-- name    : HellmanLevy.Bayes.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:59:40.666031+00:00
-- url     : https://prove2.me/theorems/034af81c-f218-4ef8-93b6-ac6715882531
-- title:
--   Lemma 4.4 — a strong Harsányi $\varepsilon$-equilibrium is a Harsányi $2M\varepsilon$-equilibrium
-- statement:
--   Let $M>0$ and $\varepsilon>0$.
--
--   1. **Graphical games.** Let $(X,G,u)$ be a graphical game with $|u|\le M$ and let $\mu$ be a measure on $X$. Every strong Harsányi $\varepsilon$-equilibrium of the game with respect to $\mu$ is a Harsányi $2M\varepsilon$-equilibrium:
--   $$\int_X\Big[\max_{a\in A}u(g,(a,\sigma_{-g}))-u(g,\sigma)\Big]\,d\mu(g)\le 2M\varepsilon .$$
--   2. **Bayesian games.** Let $B$ be a purely atomic Bayesian game with $|r^i|\le M$ for every player. If $\sigma$ is a strategy profile such that for each player $i$ there is a set $\Omega'$ with $\mu^i(\Omega')<\varepsilon$ outside which player $i$ optimizes exactly, then $\sigma$ is a Harsányi $2M\varepsilon$-equilibrium of $B$.
--
--   The constant $2M$ bounds the gain from deviating. The lemma turns the strong equilibria produced on finite pieces into ordinary Harsányi equilibria (Proposition 4.11).
--
--   **Formalization Note** The Bayesian hypothesis is the per-player form of Definition 4.2; a strong Harsányi $\varepsilon$-equilibrium with one exceptional set for all players satisfies it.
--
--   Differences from the source:
--   - generalization: σ a strong Harsányi ε-equilibrium of the Bayesian game (Definition 4.2) → for each player i some Ω' with µⁱ(Ω') < ε off which player i optimizes; reason: this per-player form is implied by both readings of Definition 4.2, in particular by IsStrongHarsanyiEq, so the clause covers the printed lemma
--   - generalization: Ω a Polish space with its Borel σ-algebra → Ω a standard Borel space; reason: every Polish space with its Borel σ-algebra is standard Borel, and every notion in the statement depends only on the measurable structure, so the statement specializes to the paper's
--   - generalization: the vertex set of a graphical game is a Polish space → the vertex set X is a standard Borel space; reason: every Polish space is standard Borel and no notion used depends on the topology of X; the associated game of §4.2 lives on the type space, which is standard Borel without a named Polish topology
--   - encoding: ∫ [gain from deviating] dµ ≤ ε → the gain is µ-integrable and its integral is ≤ ε; reason: in the paper's setting the gain is bounded and measurable, so integrability excludes nothing; it prevents the Bochner default 0 from making the test vacuous
--   - encoding: payoff u : Ω × A^Ω → ℝ continuous in the Tychonoff topology on A × A^N(g), extended multilinearly to mixed profiles → u : X → (X → A) → ℝ with each u g continuous on A^X (A discrete) and depending only on g and N(g); the mixed payoff is the integral against the product measure ⊗_h σ(h); reason: given locality, continuity on A^X is continuity on A × A^N(g); the expectation under the product measure is the multilinear extension
--   - encoding: mixed actions in ∆(A) → probability mass functions PMF A; Borel strategies are those with every coordinate g ↦ σ(g)(b) measurable; reason: A is finite, so ∆(A) is the set of probability mass functions on A
--   - encoding: a purely atomic Bayesian game (Ω, I, t, (µⁱ), A, r) with knowledge relations Eᵢ → the structure BayesianGame: Eᵢ is tⁱ_x = tⁱ_y, purely atomic is countability of its classes, the prior condition (2.2) is (µⁱ).bind tⁱ = µⁱ, payoffs are given on pure profiles; reason: the paper defines Eᵢ from the types (p.11); the second clause of (2.2) and the purely atomic types of Definition 2.9 follow from the field `knows`
--   - encoding: rⁱ(σ | τⁱ) = Σ_{ω | tⁱ(ω)=τⁱ} rⁱ(ω, σ(ω)) τⁱ(ω) (3.1) → the integral of ω' ↦ rⁱ(ω', σ(ω')) against τⁱ = tⁱ_ω; reason: τⁱ is concentrated on the countable class {ω' | tⁱ(ω') = τⁱ}, so the integral is that sum
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), Lemma 4.4, p.19; Definitions 4.1–4.3, pp.16–19

import Mathlib
import Definitions.Def_HellmanLevy_Bayes_IsHarsanyiEq
import Definitions.Def_HellmanLevy_Graphical_IsGraphicalGame
import Definitions.Def_HellmanLevy_Graphical_IsHarsanyiEqG
import Definitions.Def_HellmanLevy_Graphical_IsStrongHarsanyiEqG

namespace HellmanLevy.Bayes

universe u v w

/-- **Lemma 4.4.** A strong Harsányi ε-equilibrium of a graphical game (respectively of a
Bayesian game) whose payoffs are bounded in absolute value by `M > 0` is a Harsányi
`2M·ε`-equilibrium of the game.
1. *Graphical games*: if `(X, G, u)` is a graphical game with `|u| ≤ M`, `µ` is a measure on `X`
   and `σ` is a strong Harsányi ε-equilibrium (Definition 4.3), then `σ` is a Harsányi
   `2Mε`-equilibrium (4.4).
2. *Bayesian games*: if `|rⁱ| ≤ M` for all players and `σ` is a strategy profile such that for
   each player `i` there is a set `Ω'` with `µⁱ(Ω') < ε` off which player `i` optimizes exactly
   (Definition 4.2), then `σ` is a Harsányi `2Mε`-equilibrium (4.1).

Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), Lemma 4.4, p.19 (with Definitions 4.1–4.3, pp.16–19).

**Formalization Note** In the Bayesian clause the hypothesis is the per-player form of
Definition 4.2 (one set `Ω'` for each player), which is implied by `IsStrongHarsanyiEq`
(one set for all players), so the clause covers both readings of Definition 4.2. In the
graphical clause `µ` is any measure. -/
theorem lemma_4_4 :
    (∀ {X : Type u} [MeasurableSpace X] [StandardBorelSpace X] {A : Type v} [Fintype A]
      [Nonempty A] [MeasurableSpace A] [DiscreteMeasurableSpace A] [TopologicalSpace A]
      [DiscreteTopology A] (G : X → X → Prop) (u : X → (X → A) → ℝ)
      (μ : MeasureTheory.Measure X) (ε M : ℝ), 0 < ε → 0 < M → Graphical.IsGraphicalGame G u →
      (∀ g a, |u g a| ≤ M) → ∀ σ : X → PMF A, Graphical.IsStrongHarsanyiEqG u μ ε σ →
      Graphical.IsHarsanyiEqG u μ (2 * M * ε) σ) ∧
    (∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {I : Type v} [Fintype I]
      [Nonempty I] [DecidableEq I] {A : I → Type w} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
      (B : BayesianGame Ω I A) (ε M : ℝ), 0 < ε → 0 < M → (∀ i ω a, |B.r i ω a| ≤ M) →
      ∀ σ : ∀ i, Ω → PMF (A i), IsStrategy B σ →
      (∀ i, ∃ S : Set Ω, B.μ i S < ENNReal.ofReal ε ∧ ∀ ω ∉ S, gap B i σ ω = 0) →
      IsHarsanyiEq B (2 * M * ε) σ) := by sorry

end HellmanLevy.Bayes
