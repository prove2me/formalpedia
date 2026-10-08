-- Prove2me | Theorems.Thm_NagaevLD_LowerBound_eq_1_58
-- name    : NagaevLD.LowerBound.eq_1_58
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:18:53.006111+00:00
-- url     : https://prove2.me/theorems/62af360f-09a2-4fb3-bc26-a1e92e5557ce
-- title:
--   (1.58), p. 759 — P_j ≥ ½P(X_j ≥ 2x) if x ≥ 2B_n
-- statement:
--   Let $X_1,\dots,X_n$ be independent real random variables on a probability space $(\Omega,\mathcal F,P)$ with $EX_i=0$ and $EX_i^2<\infty$ for every $i$. Put $S_n=\sum_i X_i$, $B_n^2=\sum_i\operatorname{Var}X_i$, $B_n=(B_n^2)^{1/2}$ and, for $x>0$ and an index $j$,
--   $P_j=P(S_n\ge x,\ X_j\ge x,\ \max_{i\ne j}X_i<x)$. If $x\ge 2B_n$, then
--   $$P_j\ \ge\ \tfrac12\,P(X_j\ge 2x).$$
--
--   The probability that the sum exceeds $x$ through the single summand $X_j$ is at least half the probability that $X_j$ alone exceeds $2x$. Summed over $j$, this is the paper's lower bound for $P(S_n\ge x)$.
--
--   **Formalization Note** Square integrability of each $X_i$ stands for the page's $B_n^2<\infty$; $x>0$ is the paper's standing assumption (p. 747). The condition $\max_{i\ne j}X_i<x$ is written "$X_i<x$ for every $i\ne j$".
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 759, (1.58)

import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.LowerBound

/-- (1.58), p. 759: `P_j ≥ ½ P(X_j ≥ 2x)` if `x ≥ 2B_n`. -/
theorem eq_1_58 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun (fun i => X i) P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (x : ℝ) (hx : 0 < x) (hxB : 2 * Real.sqrt (NagaevLD.FukNagaev.Bn2 P X) ≤ x) (j : Fin n) :
    (1 / 2) * P.real {ω | 2 * x ≤ X j ω} ≤ Pj P X x j := by sorry

end NagaevLD.LowerBound
