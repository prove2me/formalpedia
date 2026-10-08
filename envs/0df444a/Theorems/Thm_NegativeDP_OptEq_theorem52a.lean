-- Prove2me | Theorems.Thm_NegativeDP_OptEq_theorem52a
-- name    : NegativeDP.OptEq.theorem52a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:23.796333+00:00
-- url     : https://prove2.me/theorems/f0cdeda1-a216-4794-8b43-d38621128079
-- title:
--   Theorem 5.2(a) (N) — the operator $U$ is monotone
-- statement:
--   Let $\pi = (f_1,f_2,\dots)$ be a Markov policy of a negative dynamic programming problem, $T_n$ the operator of $f_n$, and $Uu = \sup_n T_n u$ its associated operator on $M(S)$, the non-positive extended real-valued Borel functions on $S$. For $u,v\in M(S)$,
--   $$u \le v \quad\Longrightarrow\quad Uu \le Uv .$$
--
--   Monotonicity of $U$ is used to propagate the conservation property $Uv\ge v$ along the iterates $U^n v$ (Lemma 6.2).
--
--   The paper states Theorem 5.2 for the discounted, positive and negative cases; this item is the negative case. **Formalization Note** Inequalities are pointwise; $u\in M(S)$ and $v\in M(S)$ are explicit hypotheses (`IsNegM`).
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 879, Theorem 5.2(a)

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

/-- Strauch (1966), Theorem 5.2(a), p. 879, negative case: `U` is monotone on `M(S)`. -/
theorem theorem52a (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u v : S → EReal)
    (hu : NegativeDP.Stationary.IsNegM u) (hv : NegativeDP.Stationary.IsNegM v) (huv : ∀ s, u s ≤ v s) :
    ∀ s, U P π u s ≤ U P π v s := by sorry

end NegativeDP.OptEq
