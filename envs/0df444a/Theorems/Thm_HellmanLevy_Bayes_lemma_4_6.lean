-- Prove2me | Theorems.Thm_HellmanLevy_Bayes_lemma_4_6
-- name    : HellmanLevy.Bayes.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:00:21.667429+00:00
-- url     : https://prove2.me/theorems/5772e233-25ad-41ff-9e53-207089fd43a8
-- title:
--   Lemma 4.6 — transfer from the associated graphical game at cost $|I|^2$ (corrected: strong clause for every $\delta>|I|^2\varepsilon$)
-- statement:
--   Let $B$ be a purely atomic Bayesian game on a standard Borel state space in which all players share the finite non-empty action set $A$, let $(\Omega_T,G_T,u_T)$ with the measure $\mu_T$ of (4.5) be its associated graphical game, let $\varepsilon>0$, and let $\sigma_T$ be a strategy profile of the graphical game, inducing the Bayesian profile $\sigma^i(\omega)=\sigma_T(t^i(\omega))$.
--
--   1. If $\sigma_T$ is a Harsányi $\varepsilon$-equilibrium of the associated graphical game, the induced profile is a Harsányi $|I|^2\varepsilon$-equilibrium of $B$.
--   2. If $\sigma_T$ is a strong Harsányi $\varepsilon$-equilibrium of the associated graphical game, the induced profile is a strong Harsányi $\delta$-equilibrium of $B$ for every $\delta>|I|^2\varepsilon$.
--
--   The factor $|I|^2$ comes from $t^i_*(\mu^i)\le|I|^2\mu_T$. The lemma is the last step of the proof of the main theorem.
--
--   Differences from the source:
--   - correction: a strong Harsányi ε-equilibrium of the graphical game is a strong Harsányi |I|²·ε-equilibrium of B → … a strong Harsányi δ-equilibrium of B for every δ > |I|²·ε; reason: the printed clause fails at the boundary because Definition 4.3 allows µ_T(Ω′_T) = ε while Definition 4.2 requires µⁱ(Ω′) < ε: with one player, Ω = {0, 1}, t(ω) = δ_ω, µ = (1 − ε)δ₀ + εδ₁, A = {x, y}, r(·, x) = 1, r(·, y) = 0, σ_T(δ₀) = x, σ_T(δ₁) = y is a strong Harsányi ε-equilibrium of the graphical game but every admissible Ω′ contains state 1, of mass ε = |I|²ε
--   - reading: Definition 4.2: "for each player i there is a subset Ω′ … such that for all ω ∉ Ω′, i ∈ I" → one exceptional set for all players; reason: the quantifier "i ∈ I" follows the choice of Ω′, and the proof builds one set Ω′ = ⋃ᵢ (tⁱ)⁻¹(Ω′_T); this reading implies the per-player one, so the conclusion is the stronger of the two
--   - generalization: Ω a Polish space with its Borel σ-algebra → Ω a standard Borel space; reason: every Polish space with its Borel σ-algebra is standard Borel, and every notion in the statement depends only on the measurable structure, so the statement specializes to the paper's
--   - encoding: a purely atomic Bayesian game (Ω, I, t, (µⁱ), A, r) with knowledge relations Eᵢ → the structure BayesianGame: Eᵢ is tⁱ_x = tⁱ_y, purely atomic is countability of its classes, the prior condition (2.2) is (µⁱ).bind tⁱ = µⁱ, payoffs are given on pure profiles; reason: the paper defines Eᵢ from the types (p.11); the second clause of (2.2) and the purely atomic types of Definition 2.9 follow from the field `knows`
--   - encoding: rⁱ(σ | τⁱ) = Σ_{ω | tⁱ(ω)=τⁱ} rⁱ(ω, σ(ω)) τⁱ(ω) (3.1) → the integral of ω' ↦ rⁱ(ω', σ(ω')) against τⁱ = tⁱ_ω; reason: τⁱ is concentrated on the countable class {ω' | tⁱ(ω') = τⁱ}, so the integral is that sum
--   - encoding: Ω_T = ⊔ᵢ Ω/tⁱ ≅ ⊔ᵢ Image(tⁱ), u_T(τⁱ, σ) = rⁱ(σ | τⁱ), µ_T (4.5), the induced strategies → TypeSpace B = Σ i, range (tⁱ); u_T on pure profiles as ∫ rⁱ(ω, (a(tʲ(ω)))ⱼ) dτ(ω), extended by the product measure; µ_T = |I|⁻² Σ_{i,j} (typeOf i)_*(µʲ); σⁱ(ω) = σ_T(tⁱ(ω)); reason: the same objects; the mixed extension of u_T equals rⁱ(σ | τ) because the vertices tʲ(ω), j ∈ I, are distinct
--   - encoding: mixed actions in ∆(A) → probability mass functions PMF A; Borel strategies are those with every coordinate g ↦ σ(g)(b) measurable; reason: A is finite, so ∆(A) is the set of probability mass functions on A
--   - encoding: ∫ [gain from deviating] dµ ≤ ε → the gain is µ-integrable and its integral is ≤ ε; reason: in the paper's setting the gain is bounded and measurable, so integrability excludes nothing; it prevents the Bochner default 0 from making the test vacuous
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), Lemma 4.6, p.21 (proof pp.21–22); §4.2, p.20, eq. (4.5)

import Mathlib
import Definitions.Def_HellmanLevy_Bayes_IsHarsanyiEq
import Definitions.Def_HellmanLevy_Bayes_IsStrongHarsanyiEq
import Definitions.Def_HellmanLevy_Bayes_assocPayoff
import Definitions.Def_HellmanLevy_Bayes_assocMeasure
import Definitions.Def_HellmanLevy_Bayes_induced
import Definitions.Def_HellmanLevy_Graphical_IsHarsanyiEqG
import Definitions.Def_HellmanLevy_Graphical_IsStrongHarsanyiEqG

namespace HellmanLevy.Bayes

/-- **Lemma 4.6 (strong clause corrected: every `δ > |I|²ε`).** Let `B` be a Bayesian game in
which all players share the finite action set `A`, let `Γ_B = (Ω_T, G_T, u_T)` with the measure
`µ_T` be its associated graphical game, and let `σ_T` be a strategy profile of `Γ_B`, inducing
the Bayesian profile `σⁱ(ω) = σ_T(tⁱ(ω))`.
1. If `σ_T` is a Harsányi ε-equilibrium of `Γ_B`, then the induced profile is a Harsányi
   `|I|²·ε`-equilibrium of `B`.
2. If `σ_T` is a strong Harsányi ε-equilibrium of `Γ_B`, then the induced profile is a strong
   Harsányi δ-equilibrium of `B` for every `δ > |I|²·ε`.

Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), Lemma 4.6, p.21 (proof pp.21–22); §4.2, p.20 (the associated game and (4.5)).

**Formalization Note** Clause 2 as printed ("strong Harsányi |I|²·ε-equilibrium") fails at the
boundary, because Definition 4.3 allows `µ_T(Ω′_T) = ε` while Definition 4.2 requires
`µⁱ(Ω′) < ε`: with one player, `Ω = {0, 1}`, `t(ω) = δ_ω`, `µ = (1 − ε)δ₀ + εδ₁`, `A = {x, y}`,
`r(·, x) = 1`, `r(·, y) = 0` and `σ_T(δ₀) = x`, `σ_T(δ₁) = y`, the exceptional set must contain the
state `1`, of prior mass `ε = |I|²ε`. -/
theorem lemma_4_6 {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {I : Type*}
    [Fintype I] [Nonempty I] [DecidableEq I] {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [DiscreteMeasurableSpace A] (B : BayesianGame Ω I fun _ => A)
    (ε : ℝ) (hε : 0 < ε) (σT : TypeSpace B → PMF A) :
    (Graphical.IsHarsanyiEqG (assocPayoff B) (assocMeasure B) ε σT →
        IsHarsanyiEq B ((Fintype.card I : ℝ) ^ 2 * ε) (induced B σT)) ∧
      (Graphical.IsStrongHarsanyiEqG (assocPayoff B) (assocMeasure B) ε σT →
        ∀ δ : ℝ, (Fintype.card I : ℝ) ^ 2 * ε < δ → IsStrongHarsanyiEq B δ (induced B σT)) := by sorry

end HellmanLevy.Bayes
