-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem61
-- name    : NegativeDP.EssFinite.Supplement.theorem61
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:56:00.070801+00:00
-- url     : https://prove2.me/theorems/9c6f684d-c2ff-418a-a716-bceb52fcbb7b
-- title:
--   Theorem 6.1 (D) — if U conserves v, a π̂-generated Markov policy comes within ε of v
-- statement:
--   Discounted case. Let $\hat\pi$ be a Markov policy with operator $U$, and let $G(\hat\pi)$ be the set of $\hat\pi$-generated Markov policies (every rule $\hat\pi$-generated). If $U$ conserves $v\in M(S)$, i.e. $Uv\ge v$, and $\varepsilon>0$, then there is $\pi\in G(\hat\pi)$ with
--
--   $$
--   I(\pi)\ge v-\varepsilon .
--   $$
--
--   The negative case of this theorem is the published item `NegativeDP.OptEq.theorem61`; together with this item it covers the whole source theorem. The paper marks the discounted case as previously known (Blackwell) and proves it here.
--
--   **Formalization Note** `Disc.Conserves P π̂ v` says that $v$ is bounded and Borel and $v\le Uv$ pointwise; `IsGeneratedPlan π̂ π` is $\pi\in G(\hat\pi)$.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, N → the cases not yet published (D); the negative case is the published NegativeDP.OptEq.theorem61; reason: the negative case is already published and immutable; the two items together state the whole theorem
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 881, Theorem 6.1

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

/-- Theorem 6.1 (p. 881), discounted case: if the operator `U` of `π̂` conserves `v ∈ M(S)`
(`Uv ≥ v`) and `ε > 0`, then some `π̂`-generated Markov plan `π ∈ G(π̂)` has `I(π) ≥ v − ε`.
The negative case is the published `NegativeDP.OptEq.theorem61`. -/
theorem theorem61 (P : Problem S A) (πhat : MarkovPlan S A) (v : S → ℝ)
    (hv : Disc.Conserves P πhat v) (ε : ℝ) (hε : 0 < ε) :
    ∃ π : MarkovPlan S A, IsGeneratedPlan πhat π ∧ ∀ s, v s - ε ≤ I P π.toPlan s := by sorry

end NegativeDP.EssFinite.Supplement
