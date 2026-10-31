-- Prove2me | Theorems.Thm_KallMayerSLP_Bonferroni_eq_3_11_inclusion_exclusion
-- name    : KallMayerSLP.Bonferroni.eq_3_11_inclusion_exclusion
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:14.285783+00:00
-- url     : https://prove2.me/theorems/cadb9c8f-7332-4fd0-8c50-ad866ec19c67
-- title:
--   Inclusion–exclusion for $\mathbb P(\nu\ge1)$
-- statement:
--   For events $B_1,\dots,B_r$, $r\ge1$, on a probability space, with binomial moments $S_k$ and counting variable $\nu$,
--   $$
--   \mathbb P(\nu\ge1)=S_1-S_2+\dots+(-1)^{r-1}S_r.
--   $$
--   This is the inclusion–exclusion formula, written in terms of the binomial moments.
--
--   Differences from the source:
--   - encoding: events $B_1,\dots,B_r$ (or variables $v_1,\dots,v_r$) indexed by $1,\dots,r$ → indexed by `Fin r`, that is by $0,\dots,r-1$; reason: Lean convention; same instances
--   - encoding: the number $r$ of events $B_1,\dots,B_r$ (the dimension of $\xi$ with values in $\mathbb R^r$) is left implicit → hypothesis `1 ≤ r`; reason: the family $B_1,\dots,B_r$ starts at $B_1$, so the book has $r\ge1$; the hypothesis excludes only the empty family
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.11), p.285 (PDF 294)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_occurrenceCount

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- The inclusion–exclusion formula `ℙ(ν ≥ 1) = S₁ - S₂ + ⋯ + (-1)^(r-1) S_r`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.11), p.285 (PDF 294). -/
theorem eq_3_11_inclusion_exclusion {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) :
    μ.real {ω | 1 ≤ occurrenceCount B ω} =
      ∑ j ∈ Finset.Icc 1 r, (-1 : ℝ) ^ (j - 1) * binomialMoment μ B j := by sorry

end KallMayerSLP.Bonferroni
