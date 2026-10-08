-- Prove2me | Theorems.Thm_NegativeDP_OptEq_lemma72
-- name    : NegativeDP.OptEq.lemma72
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:19.397307+00:00
-- url     : https://prove2.me/theorems/e63859f2-048c-48df-8839-3e2d07b29c48
-- title:
--   Lemma 7.2 — the set $\Gamma$ of pairs $(s, e_\pi(s))$ is Borel
-- statement:
--   In a negative dynamic programming problem, let $X$ be the set of futures, $P(X)$ the probability measures on $X$ with the σ-field $\Sigma^*$, and $e_\pi(s)\in P(X)$ the law of the future under the policy $\pi$ from the initial state $s$. Let
--   $$\Gamma = \{(s,\nu)\in S\times P(X) : \nu = e_\pi(s)\ \text{for some policy } \pi\}.$$
--   Then $\Gamma$ is a Borel subset of $S\times P(X)$.
--
--   Together with Lemma 7.1 this makes $\{s : v^*(s) > \lambda\}$ the projection of a Borel set, hence analytic, which gives the absolute measurability of $v^*$ (Theorem 7.1).
--
--   **Formalization Note** "Some policy" ranges over every randomized history-dependent plan. The set is stated inside $S\times$ `Measure X` with the Giry σ-field; since every $e_\pi(s)$ is a probability measure and the probability measures form a measurable subset, this is the same as being Borel in $S\times P(X)$. $e_\pi(s)$ is `futureLaw` (Ionescu-Tulcea construction).
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 884, Lemma 7.2 (with the definition of Γ preceding it)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
import Definitions.Def_NegativeDP_OptEq_Futures
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.OptEq

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Strauch (1966), Lemma 7.2, p. 884: the set `Γ` of pairs `(s, ν)` such that `ν = e_π(s)` for
some plan `π` is a Borel subset of `S × P(X)`. -/
theorem lemma72 (P : NegativeDP.Stationary.Problem S A) :
    MeasurableSet {x : S × Measure (Futures S A) |
      ∃ π : Plan (S := S) (A := A), x.2 = futureLaw P π x.1} := by sorry

end NegativeDP.OptEq
