-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem84
-- name    : NegativeDP.EssFinite.Supplement.theorem84
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:03:54.128797+00:00
-- url     : https://prove2.me/theorems/441abbb2-b22a-4855-9973-c387c30403fd
-- title:
--   Theorem 8.4 (D, P; corrected: I(π) ≤ u for the printed I(π) < u) — upper bounds of all returns by an excessive u
-- statement:
--   Suppose $u\in M(S)$ and $T_au\le u$ for every action $a$. Then, in the discounted and in the positive bounded case,
--
--   $$
--   I(\pi)\le u\ \text{for all policies }\pi\iff\sup_{n\ge0}I_n(\hat\pi,u)\ge I(\hat\pi)\ \text{for all Markov policies }\hat\pi.
--   $$
--
--   The paper prints $I(\pi)<u$; its proof derives the left side from Theorem 6.5, whose conclusion is $u\ge I(\pi)$, and the strict form is false (see below). The negative case of this theorem is the published item `NegativeDP.OptEq.theorem84`; together with this item it covers the whole source theorem. Together with Theorem 8.2 it characterizes $v^*$ as the smallest such $u$ that the criterion admits.
--
--   **Formalization Note** The first conjunct is case D with Blackwell's `Ta`, `I` and `Disc.In`; the second is case P with `Pos.Ta`, `Pos.I`, `Pos.In`. "All policies" are all randomized history-dependent plans; Markov policies are `MarkovPlan`s.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, P, N → the cases not yet published (D and P); the negative case is the published NegativeDP.OptEq.theorem84; reason: the negative case is already published and immutable; the two items together state the whole theorem
--   - correction: I(π) < u for all π → I(π) ≤ u for all π; reason: with r ≡ 0 and u ≡ 0 (a discounted problem for any β and a positive bounded problem for any R) Tₐu = 0 ≤ u and every Iₙ(π̂, 0) = 0 = I(π̂), so the right side holds while I(π) < u fails; the proof (p. 887) obtains u ≥ I(π) from Theorem 6.5
--   - encoding: stages numbered from 1, β^{j−1} weights → stages numbered from 0, weight P.β ^ j; reason: index shift only; Lean stage j is the paper's stage j + 1
--   - encoding: positive bounded return I(π) in [0, R] → Pos.I = real value of the [0, ∞] sum Pos.Data.IE, bounded by R in the problem; reason: the bound makes the real value exact; no instance changes
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 887, Theorem 8.4

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

/-- Theorem 8.4 (p. 887), discounted case (first conjunct) and positive bounded case (second
conjunct), with the printed `I(π) < u` read as `I(π) ≤ u` (the proof derives it from Theorem 6.5,
whose conclusion is `u ≥ I(π)`): if `u ∈ M(S)` and `Tₐu ≤ u` for every action `a`, then
`I(π) ≤ u` for every policy `π` iff `sup_{n ≥ 0} Iₙ(π̂, u) ≥ I(π̂)` for every Markov `π̂`.
The negative case is the published `NegativeDP.OptEq.theorem84`. -/
theorem theorem84 :
    (∀ (P : Problem S A) (u : S → ℝ), IsBM u → (∀ a s, Ta P a u s ≤ u s) →
      ((∀ π : Plan (S := S) (A := A), ∀ s, I P π s ≤ u s) ↔
        (∀ πhat : MarkovPlan S A, ∀ s, I P πhat.toPlan s ≤ ⨆ n : ℕ, Disc.In P πhat.toPlan n u s))) ∧
    (∀ (P : Pos.Problem S A) (u : S → ℝ), IsBM u → (∀ a s, Pos.Ta P a u s ≤ u s) →
      ((∀ π : Plan (S := S) (A := A), ∀ s, Pos.I P π s ≤ u s) ↔
        (∀ πhat : MarkovPlan S A, ∀ s,
          Pos.I P πhat.toPlan s ≤ ⨆ n : ℕ, Pos.In P πhat.toPlan n u s))) := by sorry

end NegativeDP.EssFinite.Supplement
