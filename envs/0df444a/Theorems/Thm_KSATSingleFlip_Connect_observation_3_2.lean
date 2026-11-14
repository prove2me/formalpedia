-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_observation_3_2
-- name    : KSATSingleFlip.Connect.observation_3_2
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:17:15.879338+00:00
-- url     : https://prove2.me/theorems/e6d33c89-309a-49ef-9202-7670070b07ec
-- title:
--   Observation 3.2 — Flipping a complete forcing tree
-- statement:
--   Title: Observation 3.2 — Flipping a complete forcing tree
--
--   Let σ satisfy a finite CNF formula Φ, and let T be a complete forcing tree under σ with variable set U. If the factor graph restricted to U is acyclic, then the variables of U can be ordered by non-increasing depth, and flipping them in any such order gives a satisfying path of exactly |U| single-variable flips, ending at an assignment differing from σ precisely on U.
--
--   The restricted graph retains all clause vertices; those with no neighbor in U are isolated and do not affect acyclicity. Clauses are indexed occurrences, preserving multiplicities. This is an open formalization target.
--
--   Source: Chunyang Wang, Yitong Yin, Yixiao Yu, and Yiyao Zhang, *Single-Variable Connectivity in Random k-SAT*, Observation 3.2, printed p. 14 (PDF p. 16 of STOC 2027 submission #737), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf.
-- source:
--   Chunyang Wang, Yitong Yin, Yixiao Yu, Yiyao Zhang, Single-Variable Connectivity in Random k-SAT, STOC 2027 submission #737, Observation 3.2, printed p. 14 (PDF p. 16), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_FactorGraph

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- Observation 3.2: flipping the variables of a complete forcing tree in
non-increasing depth order gives a satisfying path if the restricted factor
graph is acyclic. Clause positions are kept distinct. -/
theorem observation_3_2 {n : ℕ} (Φ : GFormula (Fin n)) (σ : Fin n → Bool)
    (T : ForcingTree Φ σ) (hσ : σ ∈ sols Φ) (hT : T.CompleteIn Finset.univ)
    (hacyclic : ((factorGraph Φ).induce {v | match v with
      | Sum.inl u => u ∈ T.vars
      | Sum.inr _ => True}).IsAcyclic) :
    (∃ order : List (Fin n), order.Nodup ∧ order.toFinset = T.vars ∧
      order.Pairwise (fun u v => T.depth v ≤ T.depth u)) ∧
    ∀ order : List (Fin n), order.Nodup → order.toFinset = T.vars →
      order.Pairwise (fun u v => T.depth v ≤ T.depth u) →
      ∃ τ : Fin n → Bool,
        IsSatPath Φ (order.scanl (fun z u => flip z u) σ) σ τ ∧
        pathLength (order.scanl (fun z u => flip z u) σ) = T.vars.card ∧
        disagree σ τ = T.vars := by
  sorry

end KSATSingleFlip.Connect
