-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem43
-- name    : NegativeDP.EssFinite.Supplement.theorem43
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:53:18.329818+00:00
-- url     : https://prove2.me/theorems/eb4600d2-1fa4-460c-ab71-19797a516b92
-- title:
--   Theorem 4.3 (D) — a semi-Markov policy dominates any policy, and a Markov policy dominates it on average
-- statement:
--   Discounted case. For any policy $\pi$ and any probability $p$ on $S$ there are a (non-random) semi-Markov policy $\tau$ and a (non-random) Markov policy $\sigma$ such that
--
--   $$
--   I(\tau)\ge I(\pi)\quad\text{and}\quad pI(\sigma)\ge pI(\pi).
--   $$
--
--   The negative case of this theorem is the published item `NegativeDP.Stationary.theorem43`; together with this item it covers the whole source theorem. It shows that, in the discounted case, nothing is lost by restricting attention to semi-Markov policies pointwise and to Markov policies in $p$-average.
--
--   **Formalization Note** `IsSemiMarkov` and `IsMarkov` are the published policy classes of `NegativeDP.Stationary.Model` (they do not involve the return); returns are Blackwell's `I`; $pI$ is the Bochner integral of the bounded Borel function `I P π`.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, N → the cases not yet published (D); the negative case is the published NegativeDP.Stationary.theorem43; reason: the negative case is already published and immutable; the two items together state the whole theorem
--   - encoding: pI = ∫ I dp → Bochner integral ∫ s, I s ∂p of the bounded Borel function I(π); reason: I(π) is bounded and Borel, so the Bochner integral is the integral the paper means
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 877, Theorem 4.3

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

/-- Theorem 4.3 (p. 877), discounted case: for any policy `π` and `p ∈ P(S)` there are a
semi-Markov `τ` and a Markov `σ` with `I(τ) ≥ I(π)` and `pI(σ) ≥ pI(π)`. The negative case is
the published `NegativeDP.Stationary.theorem43`. -/
theorem theorem43 (P : Problem S A) (π : Plan (S := S) (A := A))
    (p : Measure S) [IsProbabilityMeasure p] :
    ∃ τ σ : Plan (S := S) (A := A), IsSemiMarkov τ ∧ IsMarkov σ ∧
      (∀ s, I P π s ≤ I P τ s) ∧ ∫ s, I P π s ∂p ≤ ∫ s, I P σ s ∂p := by sorry

end NegativeDP.EssFinite.Supplement
