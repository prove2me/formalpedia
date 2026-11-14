-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_forcing_tree_acyclic_true_unique
-- name    : KSATSingleFlip.Connect.forcing_tree_acyclic_true_unique
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:01:04.957208+00:00
-- url     : https://prove2.me/theorems/60bbe1f9-450b-463e-a8ef-0a1db4fb1a9e
-- title:
--   Acyclic forcing trees have unique true literals in each clause
-- statement:
--   Let $T$ be a forcing tree of a finite Boolean formula $\Phi$ under assignment $\sigma$. If the factor graph induced by the variables of $T$ together with all clause vertices is acyclic, then each clause of $\Phi$ has at most one literal that is true under $\sigma$ on the variables of $T$. This graph statement supplies the remaining acyclicity step in the bottom-up flip argument of Observation 3.2.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, Observation 3.2, printed p. 14 (PDF p. 16) of STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_FactorGraph

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- Acyclicity forces each clause to have at most one original true literal
among the variables of a forcing tree. -/
theorem forcing_tree_acyclic_true_unique {n : ℕ} (Φ : GFormula (Fin n)) (σ : Fin n → Bool)
    (T : ForcingTree Φ σ)
    (hacyclic : ((factorGraph Φ).induce {v | match v with
      | Sum.inl u => u ∈ T.vars
      | Sum.inr _ => True}).IsAcyclic) :
    ∀ c : Fin Φ.length, ∀ u ∈ T.vars, ∀ v ∈ T.vars,
      Φ.get c u = some (σ u) → Φ.get c v = some (σ v) → u = v := by
  sorry

end KSATSingleFlip.Connect
