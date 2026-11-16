-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_Supplement_lemma_9_1
-- name    : MultiplierAssoc206.Resolution.Supplement.lemma_9_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:33:56.836829+00:00
-- url     : https://prove2.me/theorems/00eca45c-511d-434c-8292-2c91b7eb45ac
-- title:
--   Lemma 9.1 — Frege substitution lemma
-- statement:
--   Fix a Frege system. Let $\pi$ be a derivation of a formula $G$ from a set of formulas $\Gamma$, and let $\sigma$ be a formula substitution such that every formula $\sigma(x)$ has depth at most $D$ and size at most $S$, where $S\ge 1$. Write $F^\sigma$, $\Gamma^\sigma=\{F^\sigma:F\in\Gamma\}$ and $\pi^\sigma$ for the result of applying $\sigma$ to a formula, to every formula of $\Gamma$, and to every line of $\pi$. Then $\pi^\sigma$ is a derivation of $G^\sigma$ from $\Gamma^\sigma$, and
--   $$\operatorname{depth}(\pi^\sigma)\le\operatorname{depth}(\pi)+D+1,\qquad|\pi^\sigma|\le S\cdot|\pi|.$$
--
--   This is the Frege analogue of the substitution lemma for resolution: it lets a refutation of one formula be transported to a refutation of a substituted formula with an additive loss in depth and a multiplicative loss in size, and it is applied twice in the reduction from the perfect-matching formula (Lemma 9.4).
--
--   **Formalization Note** The depth and size of $\sigma$, the maxima of $\operatorname{depth}(\sigma(x))$ and $|\sigma(x)|$, are given as uniform bounds $D$ and $S$; since every formula has size at least $1$, $S\ge 1$ holds automatically when there is at least one variable.
--
--   Differences from the source:
--   - encoding: depth(σ) and |σ|, the maxima over the variables → uniform bounds D and S on depth(σ x) and size(σ x), with 1 ≤ S; reason: the maxima are the least such bounds, so the bounds with D = depth(σ), S = |σ| give the source's statement, and 1 ≤ S excludes only an empty variable set, where the maximum has no value
--   - reading: the size of a formula is "its number of symbols" → symbols counted in prefix form (a variable 1, ¬F one more than F, a disjunction one more than its arguments together); reason: the source does not fix a notation; prefix form counts each variable occurrence and each connective once
--   - encoding: implicational completeness for every Γ → required only for finite Γ in the definition of a Frege system; reason: equivalent by the compactness theorem, so the same systems qualify
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.23 (printed p.22), Lemma 9.1 (Frege substitution lemma, cf. [CR79, Lemma 2.5])

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Supplement_Frege

set_option autoImplicit false

namespace MultiplierAssoc206.Resolution.Supplement

/-- Lemma 9.1 (Frege substitution lemma), PDF p.23 (printed p.22): in a Frege system, if `π` is a derivation of
`G` from `Γ` and `σ` is a formula substitution whose formulas `σ x` all have depth at most `D`
and size at most `S`, then `π^σ` is a derivation of `G^σ` from `Γ^σ` of depth at most
`depth(π) + D + 1` and size at most `S · |π|`. -/
theorem lemma_9_1 (R : List Rule) (hR : IsFregeSystem R) {α β : Type} (σ : α → Formula β) (D S : ℕ)
    (hD : ∀ x, (σ x).depth ≤ D) (hS : ∀ x, (σ x).size ≤ S) (hS1 : 1 ≤ S)
    (Γ : Set (Formula α)) (G : Formula α) (π : List (Formula α))
    (hπ : IsDerivation R Γ G π) :
    IsDerivation R (Formula.subst σ '' Γ) (G.subst σ) (π.map (Formula.subst σ)) ∧
      derivDepth (π.map (Formula.subst σ)) ≤ derivDepth π + D + 1 ∧
      derivSize (π.map (Formula.subst σ)) ≤ S * derivSize π := by sorry

end MultiplierAssoc206.Resolution.Supplement
