-- Prove2me | Theorems.Thm_KallMayerSLP_Bonferroni_eq_3_8_3_9_distribution_function
-- name    : KallMayerSLP.Bonferroni.eq_3_8_3_9_distribution_function
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:40.53003+00:00
-- url     : https://prove2.me/theorems/4e72e6bf-5760-47c9-ab51-9e76468a8983
-- title:
--   Distribution function as one minus the probability of a union
-- statement:
--   Let $\xi:\Omega\to\mathbb R^r$, $r\ge1$, be a random vector on a probability space, let $x\in\mathbb R^r$, and let $A_i=\{\xi_i\le x_i\}$, $B_i=A_i^c$. Then
--   $$
--   F(x)=\mathbb P(A_1\cap\dots\cap A_r)=\mathbb P\big((B_1\cup\dots\cup B_r)^c\big)=1-\mathbb P(B_1\cup\dots\cup B_r),
--   $$
--   and, with $\nu$ the number of events out of $B_1,\dots,B_r$ which occur,
--   $$
--   F(x)=1-\mathbb P(\nu\ge1).
--   $$
--   This turns bounds on the probability of a union into bounds on the distribution function.
--
--   Differences from the source:
--   - encoding: events $B_1,\dots,B_r$ (or variables $v_1,\dots,v_r$) indexed by $1,\dots,r$ → indexed by `Fin r`, that is by $0,\dots,r-1$; reason: Lean convention; same instances
--   - encoding: the number $r$ of events $B_1,\dots,B_r$ (the dimension of $\xi$ with values in $\mathbb R^r$) is left implicit → hypothesis `1 ≤ r`; reason: the family $B_1,\dots,B_r$ starts at $B_1$, so the book has $r\ge1$; the hypothesis excludes only the empty family
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.8) and (3.9), p.285 (PDF 294)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_jointCDF
import Definitions.Def_KallMayerSLP_Bonferroni_lowerEvent
import Definitions.Def_KallMayerSLP_Bonferroni_exceedanceEvent
import Definitions.Def_KallMayerSLP_Bonferroni_occurrenceCount

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- The distribution function as the complement of a union:
`F(x) = ℙ(A₁ ∩ ⋯ ∩ A_r) = ℙ((B₁ ∪ ⋯ ∪ B_r)^c) = 1 - ℙ(B₁ ∪ ⋯ ∪ B_r)` and
`F(x) = 1 - ℙ(ν ≥ 1)`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.8) and (3.9), p.285 (PDF 294). -/
theorem eq_3_8_3_9_distribution_function {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (ξ : Ω → Fin r → ℝ) (hξ : Measurable ξ) (x : Fin r → ℝ) :
    jointCDF μ ξ x = μ.real (⋂ i, lowerEvent ξ x i) ∧
    μ.real (⋂ i, lowerEvent ξ x i) = μ.real (⋃ i, exceedanceEvent ξ x i)ᶜ ∧
    μ.real (⋃ i, exceedanceEvent ξ x i)ᶜ = 1 - μ.real (⋃ i, exceedanceEvent ξ x i) ∧
    jointCDF μ ξ x = 1 - μ.real {ω | 1 ≤ occurrenceCount (exceedanceEvent ξ x) ω} := by sorry

end KallMayerSLP.Bonferroni
