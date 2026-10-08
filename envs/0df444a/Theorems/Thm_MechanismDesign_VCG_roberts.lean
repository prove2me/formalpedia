-- Prove2me | Theorems.Thm_MechanismDesign_VCG_roberts
-- name    : MechanismDesign.VCG.roberts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T03:18:11.435165+00:00
-- url     : https://prove2.me/theorems/f972a118-0b43-4acd-be34-83e9197e4639
-- title:
--   Proposition 7.7 (corrected) -- Roberts' theorem: flexible onto PAD rules on unrestricted domains are affine maximizers
-- statement:
--   In the dominant-strategy model of Chapter 7, suppose $A$ is finite and every agent's domain is unrestricted: for every agent $i$ and every vector $\nu \in \mathbb R^{A}$ there is a type $\theta_i \in \Theta_i$ with $u_i(a, \theta_i) = \nu(a)$ for all $a \in A$. Let $q$ be a flexible decision rule (its range $q(\Theta)$ has at least three elements) whose range is all of $A$, $q(\Theta) = A$. Then $q$ satisfies positive association of differences if and only if there are weights $k_i \ge 0$, not all zero, and a function $F : A \to \mathbb R$ such that for every $\theta \in \Theta$
--
--   $$
--   \sum_{i=1}^N k_i\, u_i(q(\theta), \theta_i) + F(q(\theta)) \ \ge\ \sum_{i=1}^N k_i\, u_i(a, \theta_i) + F(a) \qquad \text{for all } a \in A.
--   $$
--
--   In words: onto PAD rules on unrestricted domains are exactly the maximizers of a weighted utilitarian welfare function with an exogenous bias $F$ (Roberts 1979). The book gives no proof.
--
--   **Formalization Note** The page states the conclusion with $k_i > 0$ for every $i$ and for all $a \in A$; both are corrected, since the printed statement is false. (i) A dictatorship — $q(\theta)$ maximizes agent 1's utility, ties broken by a fixed order — is flexible and satisfies PAD, but with two or more agents it is not a weighted maximizer with all weights positive. (ii) An affine maximizer over a proper subset $B \subsetneq A$ with $\#B \ge 3$ satisfies PAD, but if the inequality had to hold for some $c \notin B$, a profile in which every agent values $c$ at a large $M$ violates it for every fixed $(k, F)$. The corrected form keeps the page's conclusion over all $a \in A$ and adds the hypothesis that $q$ is onto $A$ (the form in which Roberts' theorem is usually stated and proved, e.g. Lavi, Mu'alem and Nisan 2009), with $k_i \ge 0$ not all zero. Under the onto hypothesis flexibility amounts to $\#A \ge 3$; it is kept as on the page.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.136, Proposition 7.7 (corrected, weights k_i ≥ 0 not all zero, q onto A; see Formalization Note); Roberts (1979), The characterization of implementable choice rules

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.7 (p.136), Roberts (1979), **corrected** (see the natural-language
statement): `A` is finite and every agent's type set is unrestricted (every `ν : A → ℝ` is
`uᵢ(·, θᵢ)` for some `θᵢ`). For a flexible decision rule `q` whose range is all of `A`, `q`
satisfies PAD if and only if there are weights `kᵢ ≥ 0`, not all zero, and `F : A → ℝ` such
that for every `θ ∈ Θ`, `∑ᵢ kᵢ uᵢ(q(θ), θᵢ) + F(q(θ)) ≥ ∑ᵢ kᵢ uᵢ(a, θᵢ) + F(a)` for all
`a ∈ A`. -/
theorem roberts {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι] [Finite A]
    (u : ∀ i, A → Θ i → ℝ) (hrich : ∀ (i : ι) (ν : A → ℝ), ∃ x : Θ i, ∀ a, u i a x = ν a)
    (q : (∀ i, Θ i) → A) (hflex : Flexible q) (honto : Set.range q = Set.univ) :
    PAD u q ↔
      ∃ k : ι → ℝ, (∀ i, 0 ≤ k i) ∧ (∃ i, 0 < k i) ∧ ∃ F : A → ℝ,
        ∀ (θ : ∀ j, Θ j) (a : A),
          ∑ i, k i * u i (q θ) (θ i) + F (q θ) ≥ ∑ i, k i * u i a (θ i) + F a := by sorry

end MechanismDesign.VCG
