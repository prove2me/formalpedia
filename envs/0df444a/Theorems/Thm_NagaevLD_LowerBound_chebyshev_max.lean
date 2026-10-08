-- Prove2me | Theorems.Thm_NagaevLD_LowerBound_chebyshev_max
-- name    : NagaevLD.LowerBound.chebyshev_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:18:38.688382+00:00
-- url     : https://prove2.me/theorems/9a8d73f9-c801-43fe-8afa-62ce90aaa672
-- title:
--   §1, p. 759 — P(max_{i≠j}X_i ≥ x) ≤ B_n²/x² for centred summands
-- statement:
--   Let $X_1,\dots,X_n$ be independent real random variables on a probability space $(\Omega,\mathcal F,P)$ with $EX_i=0$ and $EX_i^2<\infty$ for every $i$, and put $B_n^2=\sum_{i=1}^n\operatorname{Var}X_i$. Then for every $x>0$ and every index $j$
--   $$P\Big(\max_{i\ne j}X_i\ge x\Big)\ \le\ \frac{B_n^2}{x^2}.$$
--
--   Each centred summand reaches $x$ with probability at most $\sigma_i^2/x^2$, and the union over $i\ne j$ costs at most the sum. Together with the previous bound this shows that, for $x\ge 2B_n$, the probability $P(S_n^j\ge-x,\max_{i\ne j}X_i<x)$ is at least $1/2$.
--
--   **Formalization Note** The page states $P(\max_{i\ne j}X_i>x)\le B_n^2/x^2$; the statement here, with $\ge x$, is stronger, follows from the same Chebyshev step, and is the form that the preceding inequality ("It is clear that") requires once $\max_{i\ne j}X_i<x$ is used as in (1.57). The event is written "there is $i\ne j$ with $X_i\ge x$". Square integrability of each $X_i$ stands for the page's $B_n^2<\infty$. Independence is the paper's standing assumption and is not needed for this bound.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 759, §1, "P(max_{i≠j}X_i > x) ≤ B_n²/x²"

import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.LowerBound

/-- §1, p. 759: `P(max_{i≠j} X_i ≥ x) ≤ B_n²/x²` (the page prints `> x`; `≥ x` is stronger and is
what the chain needs). -/
theorem chebyshev_max {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun (fun i => X i) P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (x : ℝ) (hx : 0 < x) (j : Fin n) :
    P.real {ω | ∃ i, i ≠ j ∧ x ≤ X i ω} ≤ NagaevLD.FukNagaev.Bn2 P X / x ^ 2 := by sorry

end NagaevLD.LowerBound
