-- Prove2me | Theorems.Thm_NagaevLD_LowerBound_eq_1_57
-- name    : NagaevLD.LowerBound.eq_1_57
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:58.18496+00:00
-- url     : https://prove2.me/theorems/dea4dc37-2287-4937-81b3-cced95ce1211
-- title:
--   (1.57), p. 758 — P(S_n ≥ x) ≥ Σ_j P(S_n ≥ x, X_j ≥ x, max_{i≠j}X_i < x) = Σ_j P_j
-- statement:
--   Let $X_1,\dots,X_n$ be real random variables on a probability space $(\Omega,\mathcal F,P)$, let $S_n=X_1+\dots+X_n$, and for a real number $x$ and an index $j$ put
--   $$P_j=P\Big(S_n\ge x,\ X_j\ge x,\ \max_{i\ne j}X_i<x\Big).$$
--   Then
--   $$P(S_n\ge x)\ \ge\ \sum_{j=1}^n P_j .$$
--
--   This is the first step of Nagaev's lower bound for large deviations: the event $\{S_n\ge x\}$ contains the disjoint events on which exactly one summand reaches the level $x$, so its probability dominates the sum of their probabilities. No independence, moment condition or sign condition on $x$ is needed.
--
--   **Formalization Note** The variables are only assumed measurable (the standing independence of the paper is not used here). The condition $\max_{i\ne j}X_i<x$ is written "$X_i<x$ for every $i\ne j$".
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 758, (1.57)

import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.LowerBound

/-- (1.57), p. 758: `P(S_n ≥ x) ≥ Σ_j P(S_n ≥ x, X_j ≥ x, max_{i≠j} X_i < x) = Σ_j P_j`. -/
theorem eq_1_57 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (x : ℝ) :
    ∑ j, Pj P X x j ≤ P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω} := by sorry

end NagaevLD.LowerBound
