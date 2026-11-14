-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_forcing_tree_bottom_up_satisfies
-- name    : KSATSingleFlip.Connect.forcing_tree_bottom_up_satisfies
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:57:01.1172+00:00
-- url     : https://prove2.me/theorems/24005f64-dcca-4fd8-b176-3874bc0655de
-- title:
--   Complete forcing trees preserve satisfiability under bottom-up flips
-- statement:
--   Let $\Phi$ be a finite Boolean CNF formula, $\sigma$ a satisfying assignment, and $T$ a complete forcing tree under $\sigma$. Suppose the factor graph induced by the tree variables and all clause vertices is acyclic. Flip each tree variable exactly once in any order of nonincreasing tree depth. Then every intermediate assignment satisfies $\Phi$. This is the clause-preservation assertion at the heart of Observation 3.2; together with the elementary properties of flip sequences it yields the satisfying path asserted there.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, Observation 3.2, printed p. 14 (PDF p. 16) of STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_FactorGraph

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- The clause-preservation core of Observation 3.2. -/
theorem forcing_tree_bottom_up_satisfies {n : ℕ} (Φ : GFormula (Fin n)) (σ : Fin n → Bool)
    (T : ForcingTree Φ σ) (hσ : σ ∈ sols Φ) (hT : T.CompleteIn Finset.univ)
    (hacyclic : ((factorGraph Φ).induce {v | match v with
      | Sum.inl u => u ∈ T.vars
      | Sum.inr _ => True}).IsAcyclic)
    (order : List (Fin n)) (hn : order.Nodup) (hv : order.toFinset = T.vars)
    (ho : order.Pairwise (fun u v => T.depth v ≤ T.depth u)) :
    ∀ z ∈ order.scanl (fun z u => flip z u) σ, FSat z Φ := by
  sorry

end KSATSingleFlip.Connect
