-- Prove2me | Theorems.Thm_KallMayerSLP_Bonferroni_eq_3_12_binomial_moment_distribution
-- name    : KallMayerSLP.Bonferroni.eq_3_12_binomial_moment_distribution
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:04.674889+00:00
-- url     : https://prove2.me/theorems/5487b685-f9b5-46a1-afd3-3e8cdb6c792e
-- title:
--   Binomial moments from the distribution of $\nu$
-- statement:
--   For events $B_1,\dots,B_r$, $r\ge1$, on a probability space, and $k=0,\dots,r$,
--   $$
--   S_k=\sum_{i=k}^{r}\binom{i}{k}\mathbb P(\nu=i).
--   $$
--   So the binomial moments are linear functions of the distribution of $\nu$.
--
--   Differences from the source:
--   - encoding: events $B_1,\dots,B_r$ (or variables $v_1,\dots,v_r$) indexed by $1,\dots,r$ → indexed by `Fin r`, that is by $0,\dots,r-1$; reason: Lean convention; same instances
--   - encoding: the number $r$ of events $B_1,\dots,B_r$ (the dimension of $\xi$ with values in $\mathbb R^r$) is left implicit → hypothesis `1 ≤ r`; reason: the family $B_1,\dots,B_r$ starts at $B_1$, so the book has $r\ge1$; the hypothesis excludes only the empty family
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.12), p.287 (PDF 296)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_occurrenceCount

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- The binomial moments in terms of the distribution of `ν`:
`S_k = ∑_{i=k}^r (i choose k) ℙ(ν = i)` for `k = 0, …, r`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.12), p.287 (PDF 296). -/
theorem eq_3_12_binomial_moment_distribution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) (k : ℕ) (hk : k ≤ r) :
    binomialMoment μ B k =
      ∑ i ∈ Finset.Icc k r, (i.choose k : ℝ) * μ.real {ω | occurrenceCount B ω = i} := by sorry

end KallMayerSLP.Bonferroni
