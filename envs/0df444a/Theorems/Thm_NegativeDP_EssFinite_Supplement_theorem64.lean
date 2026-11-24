-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem64
-- name    : NegativeDP.EssFinite.Supplement.theorem64
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:58:43.675803+00:00
-- url     : https://prove2.me/theorems/3dfb342a-6dc5-4d25-b57a-534507ec8d17
-- title:
--   Theorem 6.4 (D) — if a π̂-generated policy is best in G(π̂), its first rule used stationarily does as well
-- statement:
--   Discounted case. If there is $\pi^*\in G(\hat\pi)$ with $I(\pi^*)=\sup\{I(\pi)\mid\pi\in G(\hat\pi)\}$, then
--
--   $$
--   I(f^{(\infty)})=I(\pi^*),
--   $$
--
--   where $f$ is the first element of $\pi^*$. The negative case of this theorem is the published item `NegativeDP.OptEq.theorem64`; together with this item it covers the whole source theorem.
--
--   **Formalization Note** The supremum is a real `⨆` over the subtype of $\hat\pi$-generated Markov plans (non-empty, since $\hat\pi$ generates itself, and bounded). The first rule of $\pi^*$ is `πstar 0`.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, N → the cases not yet published (D); the negative case is the published NegativeDP.OptEq.theorem64; reason: the negative case is already published and immutable; the two items together state the whole theorem
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 883, Theorem 6.4

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

/-- Theorem 6.4 (p. 883), discounted case: if `π* ∈ G(π̂)` attains
`sup {I(π) | π ∈ G(π̂)}`, then `I(f^(∞)) = I(π*)`, where `f` is the first rule of `π*`.
The negative case is the published `NegativeDP.OptEq.theorem64`. -/
theorem theorem64 (P : Problem S A) (πhat πstar : MarkovPlan S A)
    (hstar : IsGeneratedPlan πhat πstar)
    (hopt : ∀ s, I P πstar.toPlan s =
      ⨆ π : {π : MarkovPlan S A // IsGeneratedPlan πhat π}, I P π.1.toPlan s) :
    ∀ s, I P (stationary (πstar 0)).toPlan s = I P πstar.toPlan s := by sorry

end NegativeDP.EssFinite.Supplement
