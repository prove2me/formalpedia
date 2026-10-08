-- Prove2me | Theorems.Thm_NegativeDP_OptEq_theorem52c
-- name    : NegativeDP.OptEq.theorem52c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:34.657556+00:00
-- url     : https://prove2.me/theorems/85a299b1-20b6-47da-bf8b-76d19de9407f
-- title:
--   Theorem 5.2(c) (N) — $U(\sup_j u_j) \ge \sup_j Uu_j$
-- statement:
--   Let $\pi$ be a Markov policy of a negative dynamic programming problem and $U$ its operator. For every sequence $u_1,u_2,\dots$ in $M(S)$,
--   $$U\Big(\sup_j u_j\Big) \ \ge\ \sup_j U u_j \qquad\text{pointwise on } S.$$
--
--   With (a) it shows that the class of functions conserved by $U$ is closed under countable suprema, which is used in Theorem 6.2.
--
--   The paper states Theorem 5.2 for the discounted, positive and negative cases; this item is the negative case. **Formalization Note** The family is indexed by $j\in\mathbb N$ (a countable family, so that $\sup_j u_j\in M(S)$); each $u_j\in M(S)$ is a hypothesis.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 879, Theorem 5.2(c)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.OptEq

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Strauch (1966), Theorem 5.2(c), p. 879, negative case: `U(supⱼ uⱼ) ≥ supⱼ Uuⱼ` for a
sequence `u₁, u₂, …` in `M(S)`. -/
theorem theorem52c (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u : ℕ → S → EReal)
    (hu : ∀ j, NegativeDP.Stationary.IsNegM (u j)) :
    ∀ s, ⨆ j, U P π (u j) s ≤ U P π (fun t => ⨆ j, u j t) s := by sorry

end NegativeDP.OptEq
