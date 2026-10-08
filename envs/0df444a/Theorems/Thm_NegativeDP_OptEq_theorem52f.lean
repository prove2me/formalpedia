-- Prove2me | Theorems.Thm_NegativeDP_OptEq_theorem52f
-- name    : NegativeDP.OptEq.theorem52f
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:41.292439+00:00
-- url     : https://prove2.me/theorems/bde167d8-332f-442c-942c-b8099dd8a0bc
-- title:
--   Theorem 5.2(f) (N) — $Tu \le Uu$ for every $\pi$-generated $f$
-- statement:
--   Let $\pi = (f_1,f_2,\dots)$ be a Markov policy of a negative dynamic programming problem and $U$ its operator. A measurable $f:S\to A$ is **$\pi$-generated** if there is a partition of $S$ into Borel sets $S_1,S_2,\dots$ with $f = f_n$ on $S_n$. For every $\pi$-generated $f$ with operator $T$ and every $u\in M(S)$,
--   $$Tu \le Uu \qquad\text{pointwise on } S.$$
--
--   So $U$ dominates the operator of every decision rule assembled from the rules of $\pi$.
--
--   The paper states Theorem 5.2 for the discounted, positive and negative cases; this item is the negative case. **Formalization Note** "$\pi$-generated" is the published predicate `DiscountedDP.Stationary.IsGenerated` (a countable Borel partition indexed by $n$, pairwise disjoint and covering $S$, with $f = f_n$ on piece $n$).
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 879, Theorem 5.2(f)

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

/-- Strauch (1966), Theorem 5.2(f), p. 879, negative case: for any `π`-generated rule `f` with
operator `T` and any `u ∈ M(S)`, `Tu ≤ Uu`. -/
theorem theorem52f (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (f : {g : S → A // Measurable g})
    (hf : IsGenerated π f) (u : S → EReal) (hu : NegativeDP.Stationary.IsNegM u) :
    ∀ s, NegativeDP.Stationary.T P f u s ≤ U P π u s := by sorry

end NegativeDP.OptEq
