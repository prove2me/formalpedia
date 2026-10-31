-- Prove2me | Theorems.Thm_KallMayerSLP_Bonferroni_eq_3_14_lp_relaxation
-- name    : KallMayerSLP.Bonferroni.eq_3_14_lp_relaxation
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:15:58.502987+00:00
-- url     : https://prove2.me/theorems/1990f65e-09ae-4d49-a38a-1787f6b3a478
-- title:
--   The linear program (3.14) bounds $\mathbb P(\nu\ge1)$
-- statement:
--   For events $B_1,\dots,B_r$, $r\ge1$, on a probability space, the point $v_i^*=\mathbb P(\nu=i)$, $i=1,\dots,r$, is feasible for the linear program (3.14) built from $S_1,S_2$, its objective value is $\mathbb P(\nu\ge1)$, and therefore
--   $$
--   V_{\min}\le\mathbb P(\nu\ge1)\le V_{\max},
--   $$
--   where $V_{\min}$ is the optimal value of (3.14) and $V_{\max}$ the optimal value of its maximization counterpart. The program (3.14) is the relaxation of (3.13) which keeps only the first and second binomial moments.
--
--   Differences from the source:
--   - encoding: events $B_1,\dots,B_r$ (or variables $v_1,\dots,v_r$) indexed by $1,\dots,r$ → indexed by `Fin r`, that is by $0,\dots,r-1$; reason: Lean convention; same instances
--   - encoding: the number $r$ of events $B_1,\dots,B_r$ (the dimension of $\xi$ with values in $\mathbb R^r$) is left implicit → hypothesis `1 ≤ r`; reason: the family $B_1,\dots,B_r$ starts at $B_1$, so the book has $r\ge1$; the hypothesis excludes only the empty family
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.14), p.288 (PDF 297)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_occurrenceCount
import Definitions.Def_KallMayerSLP_Bonferroni_lpFeasible
import Definitions.Def_KallMayerSLP_Bonferroni_lpMin
import Definitions.Def_KallMayerSLP_Bonferroni_lpMax

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- The optimal values of (3.14) and of its maximization counterpart bound `ℙ(ν ≥ 1)`: the point
`v_i* = ℙ(ν = i)`, `i = 1, …, r`, is feasible for (3.14), its objective value is `ℙ(ν ≥ 1)`, and
therefore `V_min ≤ ℙ(ν ≥ 1) ≤ V_max`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.14) and the two sentences after it, p.288 (PDF 297). -/
theorem eq_3_14_lp_relaxation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) :
    (fun i : Fin r => μ.real {ω | occurrenceCount B ω = (i : ℕ) + 1}) ∈
        lpFeasible r (binomialMoment μ B 1) (binomialMoment μ B 2) ∧
      ∑ i : Fin r, μ.real {ω | occurrenceCount B ω = (i : ℕ) + 1} =
        μ.real {ω | 1 ≤ occurrenceCount B ω} ∧
      lpMin r (binomialMoment μ B 1) (binomialMoment μ B 2) ≤
        μ.real {ω | 1 ≤ occurrenceCount B ω} ∧
      μ.real {ω | 1 ≤ occurrenceCount B ω} ≤
        lpMax r (binomialMoment μ B 1) (binomialMoment μ B 2) := by sorry

end KallMayerSLP.Bonferroni
