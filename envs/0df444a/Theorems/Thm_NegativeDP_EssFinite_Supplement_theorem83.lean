-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem83
-- name    : NegativeDP.EssFinite.Supplement.theorem83
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:03:11.90472+00:00
-- url     : https://prove2.me/theorems/2a6e1b0b-322b-4da3-bf64-7575b8d08c50
-- title:
--   Theorem 8.3 (D) — if an optimal policy exists, an optimal stationary policy exists
-- statement:
--   Discounted case. If there exists an optimal policy $\pi^*$, i.e. $I(\pi^*)\ge\sup_\pi I(\pi)$ at every state, then there exists an optimal stationary policy $f^{(\infty)}$. The negative case of this theorem is the published item `NegativeDP.Stationary.theorem83`; together with this item it covers the whole source theorem.
--
--   $$
--   \exists\,\pi^*\ \text{optimal}\ \Longrightarrow\ \exists\,f:\ I(f^{(\infty)})=v^* .
--   $$
--
--   **Formalization Note** Optimality is Blackwell's `IsOptimal`: $I(\pi)\le I(\pi^*)$ for every randomized history-dependent plan $\pi$ and every state, which is $I(\pi^*)\ge\sup_\pi I(\pi)$.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, N → the cases not yet published (D); the negative case is the published NegativeDP.Stationary.theorem83; reason: the negative case is already published and immutable; the two items together state the whole theorem
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 886, Theorem 8.3

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

/-- Theorem 8.3 (p. 886), discounted case: if there exists an optimal policy `π*` (optimal
against every randomized history-dependent policy), then there exists an optimal stationary
policy `f^(∞)`. The negative case is the published `NegativeDP.Stationary.theorem83`. -/
theorem theorem83 (P : Problem S A) (h : ∃ π : Plan (S := S) (A := A), IsOptimal P π) :
    ∃ f : {g : S → A // Measurable g}, IsOptimal P (stationary f).toPlan := by sorry

end NegativeDP.EssFinite.Supplement
