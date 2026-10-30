-- Prove2me | Theorems.Thm_MonopolyDemandUncertainty_SBSMP_lemma_2_i
-- name    : MonopolyDemandUncertainty.SBSMP.lemma_2_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:11:16.173538+00:00
-- url     : https://prove2.me/theorems/f741ed0c-4483-44cf-96ce-800b1af0956d
-- title:
--   Lemma 2(i), p. 4 (PDF 5) — under Conditions 1 and 2, every valuation of V1 lies below every valuation of V12
-- statement:
--   Consider the two-state monopoly economy with the standing assumptions and Conditions 1 and 2. Let $(x,t)$ be a deterministic BIC and EIR mechanism, $V_1$ the set of types consuming only in the low state and $V_{12}$ the set of types consuming in both states. Then
--   $$v_1 < v_{12} \qquad \text{for all } v_1 \in V_1,\ v_{12} \in V_{12}.$$
--
--   Lemma 2(i) orders the consumption sets: types that buy only in the low state are lower than types that buy in both. Together with Fact 1 it gives the interval shape used in the appendix.
--
--   **Formalization Note** Only part (i) of Lemma 2 is posed. Part (ii) concerns "the firm's optimal mechanism" and can be broken by moving a single indifferent type between sets, so it is not stated.
-- source:
--   Peck, Rampal, Optimal Monopoly Mechanisms with Demand Uncertainty, Mathematics of Operations Research (2021), Articles in Advance, doi:10.1287/moor.2020.1120, p. 4, Lemma 2(i) (proof pp. 6–7, §A.2)

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

namespace MonopolyDemandUncertainty.SBSMP

open MeasureTheory Set

/-- Lemma 2(i), p. 4 (PDF 5), proof pp. 6–7 (PDF 7–8): under Conditions 1 and 2, in a BIC and
EIR mechanism every type of `V₁` (consuming in the paper's state 1 = index `0` only) lies strictly
below every type of `V₁₂` (consuming in both states). -/
theorem lemma_2_i (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
    (M : Mechanism) (hBIC : E.IsBIC M) (hEIR : E.IsEIR M) :
    ∀ v₁ ∈ E.onlySet M 0, ∀ v₁₂ ∈ E.bothSet M, v₁ < v₁₂ := by sorry
end MonopolyDemandUncertainty.SBSMP
