-- Prove2me | Theorems.Thm_KallMayerSLP_Bonferroni_bonferroni_inequalities
-- name    : KallMayerSLP.Bonferroni.bonferroni_inequalities
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:06.507214+00:00
-- url     : https://prove2.me/theorems/7c3fc315-354a-4d12-b2d4-5771cd2c7b7e
-- title:
--   Bonferroni inequalities
-- statement:
--   For events $B_1,\dots,B_r$, $r\ge1$, on a probability space and every even integer $0\le m<r$,
--   $$
--   \sum_{j=1}^{m}(-1)^{j-1}S_j\le\mathbb P(\nu\ge1)\le\sum_{j=1}^{m+1}(-1)^{j-1}S_j.
--   $$
--   The truncations of the inclusion–exclusion sum thus alternately bound the probability of the union. For $m=0$ this is the union bound.
--
--   Differences from the source:
--   - encoding: events $B_1,\dots,B_r$ (or variables $v_1,\dots,v_r$) indexed by $1,\dots,r$ → indexed by `Fin r`, that is by $0,\dots,r-1$; reason: Lean convention; same instances
--   - encoding: the number $r$ of events $B_1,\dots,B_r$ (the dimension of $\xi$ with values in $\mathbb R^r$) is left implicit → hypothesis `1 ≤ r`; reason: the family $B_1,\dots,B_r$ starts at $B_1$, so the book has $r\ge1$; the hypothesis excludes only the empty family
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, p.286 (PDF 295)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_occurrenceCount

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- The Bonferroni inequalities: for every even integer `0 ≤ m < r`,
`∑_{j=1}^m (-1)^(j-1) S_j ≤ ℙ(ν ≥ 1) ≤ ∑_{j=1}^(m+1) (-1)^(j-1) S_j`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, §3.4, p.286 (PDF 295). -/
theorem bonferroni_inequalities {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) (m : ℕ) (hm : Even m) (hmr : m < r) :
    ∑ j ∈ Finset.Icc 1 m, (-1 : ℝ) ^ (j - 1) * binomialMoment μ B j ≤
        μ.real {ω | 1 ≤ occurrenceCount B ω} ∧
      μ.real {ω | 1 ≤ occurrenceCount B ω} ≤
        ∑ j ∈ Finset.Icc 1 (m + 1), (-1 : ℝ) ^ (j - 1) * binomialMoment μ B j := by sorry

end KallMayerSLP.Bonferroni
