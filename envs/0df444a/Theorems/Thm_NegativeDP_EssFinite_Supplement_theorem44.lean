-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem44
-- name    : NegativeDP.EssFinite.Supplement.theorem44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:54:04.454953+00:00
-- url     : https://prove2.me/theorems/3bf69047-dd01-4dd1-9d5b-4578966c7cdf
-- title:
--   Theorem 4.4 (P) — a semi-Markov policy ε-dominates any policy, and a Markov policy ε-dominates it on average
-- statement:
--   Positive bounded case. For any policy $\pi$, any $\varepsilon>0$ and any probability $p$ on $S$ there are a (non-random) semi-Markov policy $\tau$ and a (non-random) Markov policy $\sigma$ such that
--
--   $$
--   I(\tau)\ge I(\pi)-\varepsilon\quad\text{and}\quad pI(\sigma)\ge pI(\pi)-\varepsilon.
--   $$
--
--   This is the positive bounded counterpart of Theorem 4.3; it is used in the proof of Theorem 8.1 in case P. The paper states it for case P only.
--
--   **Formalization Note** `Pos.Problem` carries the uniform bound $R$ on all expected returns; `Pos.I` is the real return. The first inequality is pointwise in the initial state, the second compares Bochner integrals over $p$ of bounded Borel functions.
--
--   Differences from the source:
--   - encoding: positive bounded return I(π) in [0, R] → Pos.I = real value of the [0, ∞] sum Pos.Data.IE, bounded by R in the problem; reason: the bound makes the real value exact; no instance changes
--   - encoding: pI = ∫ I dp → Bochner integral ∫ s, I s ∂p of the bounded Borel function I(π); reason: I(π) is bounded and Borel, so the Bochner integral is the integral the paper means
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 878, Theorem 4.4

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

/-- Theorem 4.4 (p. 878), positive bounded case: for any policy `π`, any `ε > 0` and any
`p ∈ P(S)` there are a semi-Markov `τ` and a Markov `σ` with `I(τ) ≥ I(π) − ε` and
`pI(σ) ≥ pI(π) − ε`. -/
theorem theorem44 (P : Pos.Problem S A) (π : Plan (S := S) (A := A)) (ε : ℝ) (hε : 0 < ε)
    (p : Measure S) [IsProbabilityMeasure p] :
    ∃ τ σ : Plan (S := S) (A := A), IsSemiMarkov τ ∧ IsMarkov σ ∧
      (∀ s, Pos.I P π s - ε ≤ Pos.I P τ s) ∧
      ∫ s, Pos.I P π s ∂p - ε ≤ ∫ s, Pos.I P σ s ∂p := by sorry

end NegativeDP.EssFinite.Supplement
