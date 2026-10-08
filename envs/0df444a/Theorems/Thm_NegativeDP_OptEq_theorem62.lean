-- Prove2me | Theorems.Thm_NegativeDP_OptEq_theorem62
-- name    : NegativeDP.OptEq.theorem62
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:15.985558+00:00
-- url     : https://prove2.me/theorems/46584b1f-6e39-440d-bd46-fce4232e165f
-- title:
--   Theorem 6.2 (N) — a Markov policy nearly dominating a sequence of Markov policies
-- statement:
--   In a negative dynamic programming problem, let $\pi^1,\pi^2,\dots$ be any sequence of Markov policies and $\varepsilon>0$. Then there is a Markov policy $\pi^*$ such that, at every state $s$,
--   $$I(\pi^*)(s) \ \ge\ \sup_j I(\pi^j)(s) - \varepsilon,$$
--   and the inequality is strict at every $s$ with $\sup_j I(\pi^j)(s) > -\infty$.
--
--   The paper prints this as $I(\pi^*) > \sup_j I(\pi_j) - \varepsilon$. At a state where $\sup_j I(\pi^j)(s) = -\infty$ the strict inequality would read $-\infty < I(\pi^*)(s)$, which can fail (all policies may have return $-\infty$ there), and the paper's proof gives "$I(\pi^*) \ge v-\varepsilon \ge \sup_j I(\pi^j) - \varepsilon$". We state the non-strict inequality everywhere and the strict one wherever the supremum is finite, which is the content of the printed claim. ("$\sup_j I(\pi_j)$" in the print refers to the policies $\pi^j$.)
--
--   This countable-improvement property is the step that upgrades Markov policies which are good on average into one Markov policy that is $(p,\varepsilon)$-optimal (Theorem 8.1).
--
--   The paper states this for the discounted (previously known) and negative cases; this item is the negative case. **Formalization Note** Values are in `EReal`; "Markov policy" is `MarkovPlan`, run as a deterministic plan.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 882, Theorem 6.2

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

/-- Strauch (1966), Theorem 6.2, p. 882, negative case: for any sequence of Markov plans `πʲ`
and `ε > 0` there is a Markov plan `π*` with `I(π*) ≥ supⱼ I(πʲ) − ε` everywhere, strictly
wherever `supⱼ I(πʲ) > −∞`. -/
theorem theorem62 (P : NegativeDP.Stationary.Problem S A) (πs : ℕ → MarkovPlan S A) (ε : ℝ) (hε : 0 < ε) :
    ∃ πstar : MarkovPlan S A, ∀ s,
      (⨆ j, NegativeDP.Stationary.I P (πs j).toPlan s) - (ε : EReal) ≤ NegativeDP.Stationary.I P πstar.toPlan s ∧
      ((⨆ j, NegativeDP.Stationary.I P (πs j).toPlan s) ≠ ⊥ →
        (⨆ j, NegativeDP.Stationary.I P (πs j).toPlan s) - (ε : EReal) < NegativeDP.Stationary.I P πstar.toPlan s) := by sorry

end NegativeDP.OptEq
