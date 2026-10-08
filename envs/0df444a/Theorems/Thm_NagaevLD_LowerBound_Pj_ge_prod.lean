-- Prove2me | Theorems.Thm_NagaevLD_LowerBound_Pj_ge_prod
-- name    : NagaevLD.LowerBound.Pj_ge_prod
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:18:52.274713+00:00
-- url     : https://prove2.me/theorems/43e99aa8-8a84-438c-b3a1-f36c5463874b
-- title:
--   §1, p. 758, after (1.57) — P_j ≥ P(X_j ≥ 2x) P(S_n^j ≥ −x, max_{i≠j}X_i < x)
-- statement:
--   Let $X_1,\dots,X_n$ be independent real random variables on a probability space $(\Omega,\mathcal F,P)$, let $S_n=\sum_i X_i$ and $S_n^j=\sum_{i\ne j}X_i=S_n-X_j$, and let $x>0$. With
--   $P_j=P(S_n\ge x,\ X_j\ge x,\ \max_{i\ne j}X_i<x)$, for every index $j$
--   $$P_j\ \ge\ P(X_j\ge 2x)\,P\Big(S_n^j\ge -x,\ \max_{i\ne j}X_i<x\Big).$$
--
--   This bound separates the large summand $X_j$ from the rest of the sum: if $X_j$ is at least $2x$ while the other summands stay below $x$ and their sum is at least $-x$, then $S_n\ge x$ and $X_j$ is the only summand at level $x$. It is the step that turns $P_j$ into a product of a single-summand tail and a probability close to one.
--
--   **Formalization Note** The page writes this as a chain $P_j\ge\int_{u\ge-x}P(X_j\ge\max[x,x-u])\,dP(S_n^j<u,\max_{i\ne j}X_i<x)\ge P(X_j\ge2x)P(S_n^j\ge-x,\max_{i\ne j}X_i<x)$; the formal statement is the outer inequality. The condition $\max_{i\ne j}X_i<x$ is written "$X_i<x$ for every $i\ne j$".
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 758, §1, after (1.57)

import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.LowerBound

/-- §1, p. 758, after (1.57): `P_j ≥ P(X_j ≥ 2x) P(S_n^j ≥ −x, max_{i≠j} X_i < x)`. -/
theorem Pj_ge_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun (fun i => X i) P)
    (x : ℝ) (hx : 0 < x) (j : Fin n) :
    P.real {ω | 2 * x ≤ X j ω} *
        P.real {ω | -x ≤ Sj n X j ω ∧ ∀ i, i ≠ j → X i ω < x} ≤ Pj P X x j := by sorry

end NagaevLD.LowerBound
