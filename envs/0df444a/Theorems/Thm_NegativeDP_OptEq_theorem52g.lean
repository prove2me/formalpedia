-- Prove2me | Theorems.Thm_NegativeDP_OptEq_theorem52g
-- name    : NegativeDP.OptEq.theorem52g
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:37.525459+00:00
-- url     : https://prove2.me/theorems/0162689f-66bd-4a70-8ed7-1912bff85672
-- title:
--   Theorem 5.2(g) (N) — a $\pi$-generated $f$ with $Tu \ge Uu - \varepsilon$
-- statement:
--   Let $\pi$ be a Markov policy of a negative dynamic programming problem and $U$ its operator. For every $u\in M(S)$ and every $\varepsilon>0$ there is a $\pi$-generated measurable $f:S\to A$ whose operator $T$ satisfies
--   $$Tu(s) \ \ge\ Uu(s) - \varepsilon \qquad\text{for all } s\in S.$$
--
--   This is the selection step that turns the supremum $Uu=\sup_n T_n u$ into a single decision rule; it drives the construction of nearly optimal Markov policies in Theorem 6.1.
--
--   The paper states Theorem 5.2 for the discounted, positive and negative cases; this item is the negative case. **Formalization Note** At a state where $Uu(s) = -\infty$ the inequality is automatic ($-\infty - \varepsilon = -\infty$ in `EReal`). "$\pi$-generated" is the published predicate `DiscountedDP.Stationary.IsGenerated`.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 879, Theorem 5.2(g)

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

/-- Strauch (1966), Theorem 5.2(g), p. 879, negative case: for any `u ∈ M(S)` and `ε > 0` there
is a `π`-generated rule `f` whose operator satisfies `Tu ≥ Uu − ε` at every state. -/
theorem theorem52g (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u : S → EReal) (hu : NegativeDP.Stationary.IsNegM u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : {g : S → A // Measurable g}, IsGenerated π f ∧
      ∀ s, U P π u s - (ε : EReal) ≤ NegativeDP.Stationary.T P f u s := by sorry

end NegativeDP.OptEq
