-- Prove2me | Theorems.Thm_NagaevLD_LowerBound_clear_step
-- name    : NagaevLD.LowerBound.clear_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:18:25.038671+00:00
-- url     : https://prove2.me/theorems/0c84da3b-1903-4426-9b87-6a36a2ed7922
-- title:
--   §1, p. 759, "It is clear that" — P(S_n^j ≥ −x, max_{i≠j}X_i < x) ≥ P(S_n^j ≥ −x) − P(max_{i≠j}X_i ≥ x)
-- statement:
--   Let $X_1,\dots,X_n$ be real random variables on a probability space $(\Omega,\mathcal F,P)$, let $S_n^j=\sum_{i\ne j}X_i$, let $x$ be real and $j$ an index. Then
--   $$P\Big(S_n^j\ge -x,\ \max_{i\ne j}X_i<x\Big)\ \ge\ P\big(S_n^j\ge -x\big)-P\Big(\max_{i\ne j}X_i\ge x\Big).$$
--
--   This is the elementary inequality $P(A\cap B^{c})\ge P(A)-P(B)$ applied to $A=\{S_n^j\ge-x\}$ and $B=\{\max_{i\ne j}X_i\ge x\}$. It reduces the probability on the right-hand side of the bound on $P_j$ to two one-sided tail probabilities, each of which is controlled by Chebyshev's inequality.
--
--   **Formalization Note** The page prints "$\max_{i\ne j}X_i\le x$" on the left and "$\max_{i\ne j}X_i>x$" on the right, while (1.57) and the bound on $P_j$ use $\max_{i\ne j}X_i<x$. The statement here uses $<x$ on the left and therefore $\ge x$ on the right, which is the form the argument needs. The event $\{\max_{i\ne j}X_i\ge x\}$ is written "there is $i\ne j$ with $X_i\ge x$".
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 759, §1, "It is clear that" (before (1.58))

import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.LowerBound

/-- §1, p. 759, "It is clear that": `P(S_n^j ≥ −x, max_{i≠j} X_i < x) ≥ P(S_n^j ≥ −x) − P(max_{i≠j} X_i ≥ x)`
(the page prints `≤ x` and `> x`; this is the form the chain uses with (1.57)'s `< x`). -/
theorem clear_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (x : ℝ) (j : Fin n) :
    P.real {ω | -x ≤ Sj n X j ω} - P.real {ω | ∃ i, i ≠ j ∧ x ≤ X i ω} ≤
      P.real {ω | -x ≤ Sj n X j ω ∧ ∀ i, i ≠ j → X i ω < x} := by sorry

end NagaevLD.LowerBound
