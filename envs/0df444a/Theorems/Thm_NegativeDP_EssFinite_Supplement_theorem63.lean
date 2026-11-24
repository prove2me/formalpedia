-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem63
-- name    : NegativeDP.EssFinite.Supplement.theorem63
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:57:46.158822+00:00
-- url     : https://prove2.me/theorems/847ff203-8a22-4e4d-90bd-b714f7a5c869
-- title:
--   Theorem 6.3 (D) — an N-stationary π̂-generated policy comes within ε of any π̂-generated policy
-- statement:
--   Discounted case. If $\pi\in G(\hat\pi)$, then for any $N$ and any $\varepsilon>0$ there is $\pi^*\in G(\hat\pi)$ which is $N$-stationary ($f_n=f$ for some $f$ and all $n\le N$) and satisfies
--
--   $$
--   I(\pi^*)\ge I(\pi)-\varepsilon .
--   $$
--
--   The negative case of this theorem is the published item `NegativeDP.OptEq.theorem63`; together with this item it covers the whole source theorem.
--
--   **Formalization Note** `IsNStationary π* N` requires `π* k = f` for the Lean rules `k < N`, i.e. the paper's $f_1,\dots,f_N$; for $N=0$ it is vacuous, as in the paper.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, N → the cases not yet published (D); the negative case is the published NegativeDP.OptEq.theorem63; reason: the negative case is already published and immutable; the two items together state the whole theorem
--   - encoding: stages numbered from 1, β^{j−1} weights → stages numbered from 0, weight P.β ^ j; reason: index shift only; Lean stage j is the paper's stage j + 1
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 883, Theorem 6.3

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

/-- Theorem 6.3 (p. 883), discounted case: for `π ∈ G(π̂)`, any `N` and `ε > 0` there is an
`N`-stationary `π* ∈ G(π̂)` with `I(π*) ≥ I(π) − ε`. The negative case is the published
`NegativeDP.OptEq.theorem63`. -/
theorem theorem63 (P : Problem S A) (πhat π : MarkovPlan S A) (hπ : IsGeneratedPlan πhat π)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ πstar : MarkovPlan S A, IsGeneratedPlan πhat πstar ∧ IsNStationary πstar N ∧
      ∀ s, I P π.toPlan s - ε ≤ I P πstar.toPlan s := by sorry

end NegativeDP.EssFinite.Supplement
