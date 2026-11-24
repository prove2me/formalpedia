-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem62
-- name    : NegativeDP.EssFinite.Supplement.theorem62
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:56:48.502804+00:00
-- url     : https://prove2.me/theorems/52144766-7e39-485c-ae44-08006aca3304
-- title:
--   Theorem 6.2 (D) — every sequence of Markov policies is strictly ε-dominated by one Markov policy
-- statement:
--   Discounted case. Let $\pi^j$, $j=1,2,\dots$, be any sequence of Markov policies. Then for any $\varepsilon>0$ there is a Markov policy $\pi^*$ with
--
--   $$
--   I(\pi^*)>\sup_j I(\pi^j)-\varepsilon
--   $$
--
--   at every state. The negative case of this theorem is the published item `NegativeDP.OptEq.theorem62`; together with this item it covers the whole source theorem. In the discounted case all returns are finite, so the strict inequality is stated everywhere, as printed.
--
--   **Formalization Note** The supremum is a real `⨆` over $j$; it is finite because $|I(\pi)|\le\sup|r|/(1-\beta)$.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, N → the cases not yet published (D); the negative case is the published NegativeDP.OptEq.theorem62; reason: the negative case is already published and immutable; the two items together state the whole theorem
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 882, Theorem 6.2

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_EssFinite_Supplement_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan Problem I T Ta U optReturn IsOptimal IsBM supNorm stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.EssFinite.Supplement

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 6.2 (p. 882), discounted case: for any sequence of Markov plans `πʲ` and `ε > 0`
there is a Markov plan `π*` with `I(π*) > supⱼ I(πʲ) − ε` at every state. The negative case is
the published `NegativeDP.OptEq.theorem62`. -/
theorem theorem62 (P : Problem S A) (πs : ℕ → MarkovPlan S A) (ε : ℝ) (hε : 0 < ε) :
    ∃ πstar : MarkovPlan S A, ∀ s,
      (⨆ j, I P (πs j).toPlan s) - ε < I P πstar.toPlan s := by sorry

end NegativeDP.EssFinite.Supplement
