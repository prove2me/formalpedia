-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem42
-- name    : NegativeDP.EssFinite.Supplement.theorem42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:52:56.981498+00:00
-- url     : https://prove2.me/theorems/d1f196ac-6d3c-4e6f-a380-1286076c25e0
-- title:
--   Theorem 4.2 (D) — eventual domination by splices implies domination by the infinite policy
-- statement:
--   Discounted case. Let $\pi$ and $\sigma$ be policies, and write $\pi^n\sigma=\{\pi_1,\dots,\pi_n,\sigma_{n+1},\dots\}$ for the policy that follows $\pi$ for $n$ stages and then switches to $\sigma$. If there is an $n_0$ with $I(\pi^n\sigma)\ge I(\sigma)$ for all $n\ge n_0$, then
--
--   $$
--   I(\pi)\ge I(\sigma).
--   $$
--
--   The negative case of this theorem is the published item `NegativeDP.Stationary.theorem42`; together with this item it covers the whole source theorem. The theorem is used to pass from finite-stage improvements to the infinite-horizon comparison in Theorem 4.3.
--
--   **Formalization Note** `switchAt π n σ` (published in `NegativeDP.Stationary.Model`) uses `π.κ k` for Lean decisions `k < n` and `σ.κ k` afterwards, i.e. the paper's $\pi^n\sigma$. Returns are Blackwell's; inequalities are pointwise in the initial state.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, N → the cases not yet published (D); the negative case is the published NegativeDP.Stationary.theorem42; reason: the negative case is already published and immutable; the two items together state the whole theorem
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 877, Theorem 4.2

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_Stationary_Model
import Definitions.Def_NegativeDP_EssFinite_Supplement_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan Problem I T Ta U optReturn IsOptimal IsBM supNorm stationary IsGenerated IsGeneratedPlan)
open NegativeDP.Stationary (switchAt prefixPlan IsSemiMarkov IsMarkov IsRandomSemiMarkov IsRandomMarkov)

namespace NegativeDP.EssFinite.Supplement

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 4.2 (p. 877), discounted case: if `I(π^nσ) ≥ I(σ)` for all `n ≥ n₀`, then
`I(π) ≥ I(σ)`. Here `π^nσ = switchAt π n σ` follows `π` for `n` stages, then `σ`. The negative
case is the published `NegativeDP.Stationary.theorem42`. -/
theorem theorem42 (P : Problem S A) (π σ : Plan (S := S) (A := A))
    (h : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ s, I P σ s ≤ I P (switchAt π n σ) s) :
    ∀ s, I P σ s ≤ I P π s := by sorry

end NegativeDP.EssFinite.Supplement
