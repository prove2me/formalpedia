-- Prove2me | Theorems.Thm_KallMayerSLP_Bonferroni_lp_feasible_nonempty_bounded
-- name    : KallMayerSLP.Bonferroni.lp_feasible_nonempty_bounded
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:32.319012+00:00
-- url     : https://prove2.me/theorems/cc7d79d1-50f5-470d-9d06-20bcb0dce402
-- title:
--   The feasible domain of (3.14) is non-empty and bounded
-- statement:
--   For events $B_1,\dots,B_r$, $r\ge1$, on a probability space, the feasible set of the linear program (3.14) built from their binomial moments $S_1,S_2$ is non-empty and bounded. Consequently (3.14) and its maximization counterpart have optimal solutions.
--
--   Differences from the source:
--   - encoding: events $B_1,\dots,B_r$ (or variables $v_1,\dots,v_r$) indexed by $1,\dots,r$ → indexed by `Fin r`, that is by $0,\dots,r-1$; reason: Lean convention; same instances
--   - encoding: the number $r$ of events $B_1,\dots,B_r$ (the dimension of $\xi$ with values in $\mathbb R^r$) is left implicit → hypothesis `1 ≤ r`; reason: the family $B_1,\dots,B_r$ starts at $B_1$, so the book has $r\ge1$; the hypothesis excludes only the empty family
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, p.288 (PDF 297)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_lpFeasible

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- The feasible domain of (3.14) is non-empty and bounded.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, §3.4, p.288 (PDF 297). -/
theorem lp_feasible_nonempty_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) :
    (lpFeasible r (binomialMoment μ B 1) (binomialMoment μ B 2)).Nonempty ∧
      Bornology.IsBounded (lpFeasible r (binomialMoment μ B 1) (binomialMoment μ B 2)) := by sorry

end KallMayerSLP.Bonferroni
