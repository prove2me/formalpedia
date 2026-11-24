-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem65
-- name    : NegativeDP.EssFinite.Supplement.theorem65
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:59:46.9578+00:00
-- url     : https://prove2.me/theorems/9958d012-dafe-4d79-81fc-d3121dfc93db
-- title:
--   Theorem 6.5 (D, P) — for excessive u, u bounds the returns of G(π̂) iff sup_n I_n(π, u) does
-- statement:
--   Suppose $u\in M(S)$ is excessive for $U$, i.e. $Uu\le u$. Then, in the discounted and in the positive bounded case,
--
--   $$
--   u\ge I(\pi)\ \text{for all }\pi\in G(\hat\pi)\iff\sup_{n\ge0}I_n(\pi,u)\ge I(\pi)\ \text{for all }\pi\in G(\hat\pi).
--   $$
--
--   The negative case of this theorem is the published item `NegativeDP.OptEq.theorem65`; together with this item it covers the whole source theorem. The paper marks cases D and P as previously known and proves the result here; it is the criterion behind Theorem 8.4.
--
--   **Formalization Note** The first conjunct is case D with `Disc.In` and `Disc.IsExcessive`, the second case P with `Pos.In` and `Pos.IsExcessive`. $\sup_{n\ge0}$ is a real `⨆ n : ℕ`, finite because $I_n(\pi,u)$ is bounded uniformly in $n$; $n=0$ gives $I_0(\pi,u)=u$.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, P, N → the cases not yet published (D and P); the negative case is the published NegativeDP.OptEq.theorem65; reason: the negative case is already published and immutable; the two items together state the whole theorem
--   - encoding: stages numbered from 1, β^{j−1} weights → stages numbered from 0, weight P.β ^ j; reason: index shift only; Lean stage j is the paper's stage j + 1
--   - encoding: positive bounded return I(π) in [0, R] → Pos.I = real value of the [0, ∞] sum Pos.Data.IE, bounded by R in the problem; reason: the bound makes the real value exact; no instance changes
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 883, Theorem 6.5

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

/-- Theorem 6.5 (p. 883), discounted case (first conjunct) and positive bounded case (second
conjunct): for `u ∈ M(S)` excessive for `U` (`Uu ≤ u`), `u ≥ I(π)` for all `π ∈ G(π̂)` if and
only if `sup_{n ≥ 0} Iₙ(π, u) ≥ I(π)` for all `π ∈ G(π̂)`. The negative case is the published
`NegativeDP.OptEq.theorem65`. -/
theorem theorem65 :
    (∀ (P : Problem S A) (πhat : MarkovPlan S A) (u : S → ℝ), IsBM u →
      Disc.IsExcessive P πhat u →
      ((∀ π : MarkovPlan S A, IsGeneratedPlan πhat π → ∀ s, I P π.toPlan s ≤ u s) ↔
        (∀ π : MarkovPlan S A, IsGeneratedPlan πhat π →
          ∀ s, I P π.toPlan s ≤ ⨆ n : ℕ, Disc.In P π.toPlan n u s))) ∧
    (∀ (P : Pos.Problem S A) (πhat : MarkovPlan S A) (u : S → ℝ), IsBM u →
      Pos.IsExcessive P πhat u →
      ((∀ π : MarkovPlan S A, IsGeneratedPlan πhat π → ∀ s, Pos.I P π.toPlan s ≤ u s) ↔
        (∀ π : MarkovPlan S A, IsGeneratedPlan πhat π →
          ∀ s, Pos.I P π.toPlan s ≤ ⨆ n : ℕ, Pos.In P π.toPlan n u s))) := by sorry

end NegativeDP.EssFinite.Supplement
