-- Prove2me | Theorems.Thm_NagaevLD_LowerBound_lower_bound
-- name    : NagaevLD.LowerBound.lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:18:53.385227+00:00
-- url     : https://prove2.me/theorems/5615d2f7-edef-42e3-aee3-90f66c2e137d
-- title:
--   §1, p. 759, after (1.58) — for EX_i = 0, B_n² < ∞ and x ≥ 2B_n, P(S_n ≥ x) ≥ ½ΣP(X_j ≥ 2x)
-- statement:
--   Let $X_1,\dots,X_n$ be independent real random variables on a probability space $(\Omega,\mathcal F,P)$ with
--   $$EX_i=0\quad(i=1,\dots,n),\qquad B_n^2=\sum_{i=1}^n\operatorname{Var}X_i<\infty ,$$
--   and let $S_n=X_1+\dots+X_n$ and $B_n=(B_n^2)^{1/2}$. Then for every $x\ge 2B_n$ with $x>0$,
--   $$P(S_n\ge x)\ \ge\ \frac12\sum_{j=1}^n P(X_j\ge 2x).$$
--
--   This is the lower bound that closes §1 of Nagaev's survey. It holds without assuming that the summands are identically distributed or that their tails are regularly varying, and it complements the paper's upper bounds of Fuk–Nagaev type, which have the form $P(S_n\ge x)\le\sum_jP(X_j>y_j)+\dots$: in the range $x\ge 2B_n$ the probability of a large deviation of the sum is, up to the factor $\tfrac12$ and the change from $x$ to $2x$, at least the probability that one summand alone is large.
--
--   **Formalization Note** The page's hypothesis $B_n^2<\infty$ is stated as "each $X_i$ is square integrable" (Lean's `MemLp (X i) 2 P`), since Mathlib's variance of a non-square-integrable variable is $0$. The level $x$ is positive, as everywhere in the paper (p. 747). The summands are indexed by `Fin n`.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), pp. 758–759, §1, the lower bound after (1.58)

import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.LowerBound

/-- §1, p. 759, after (1.58): for `EX_i = 0`, `B_n² < ∞` and `x ≥ 2B_n`,
`P(S_n ≥ x) ≥ ½ Σ_j P(X_j ≥ 2x)`. -/
theorem lower_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun (fun i => X i) P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (x : ℝ) (hx : 0 < x) (hxB : 2 * Real.sqrt (NagaevLD.FukNagaev.Bn2 P X) ≤ x) :
    (1 / 2) * ∑ j, P.real {ω | 2 * x ≤ X j ω} ≤ P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω} := by sorry

end NagaevLD.LowerBound
