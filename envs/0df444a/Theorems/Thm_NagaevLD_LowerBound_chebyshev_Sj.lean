-- Prove2me | Theorems.Thm_NagaevLD_LowerBound_chebyshev_Sj
-- name    : NagaevLD.LowerBound.chebyshev_Sj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:02.542253+00:00
-- url     : https://prove2.me/theorems/41242bf3-aa74-4325-a347-ccfdf91bdba2
-- title:
--   §1, p. 759 — P(S_n^j ≥ −x) ≥ 1 − B_n²/x² for centred summands
-- statement:
--   Let $X_1,\dots,X_n$ be independent real random variables on a probability space $(\Omega,\mathcal F,P)$ with $EX_i=0$ and $EX_i^2<\infty$ for every $i$. Write $\sigma_i^2=\operatorname{Var}X_i$, $B_n^2=\sum_{i=1}^n\sigma_i^2$ and $S_n^j=\sum_{i\ne j}X_i$. Then for every $x>0$ and every index $j$
--   $$P\big(S_n^j\ge -x\big)\ \ge\ 1-\frac{B_n^2}{x^2}.$$
--
--   The sum of the summands other than $X_j$ has variance $\sum_{i\ne j}\sigma_i^2\le B_n^2$, so it falls below $-x$ with probability at most $B_n^2/x^2$. In Nagaev's lower bound this keeps the rest of the sum from cancelling a large summand $X_j$.
--
--   **Formalization Note** The hypothesis $B_n^2<\infty$ of the page is stated as "each $X_i$ is square integrable" (Lean's `MemLp (X i) 2 P`); without it Mathlib's variance of a non-square-integrable variable is $0$ and the bound would be false.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 759, §1, "On the other hand, P(S_n^j ≥ −x) ≥ 1 − B_n²/x²"

import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.LowerBound

/-- §1, p. 759: `P(S_n^j ≥ −x) ≥ 1 − B_n²/x²` for centred, square-integrable, independent summands. -/
theorem chebyshev_Sj {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun (fun i => X i) P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (x : ℝ) (hx : 0 < x) (j : Fin n) :
    1 - NagaevLD.FukNagaev.Bn2 P X / x ^ 2 ≤ P.real {ω | -x ≤ Sj n X j ω} := by sorry

end NagaevLD.LowerBound
