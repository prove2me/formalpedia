-- Prove2me | Theorems.Thm_KallMayerSLP_Bonferroni_binomial_moment_one_marginals
-- name    : KallMayerSLP.Bonferroni.binomial_moment_one_marginals
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:19.978597+00:00
-- url     : https://prove2.me/theorems/fadcfbc5-93ff-458e-9f7e-26bc7fa5e848
-- title:
--   $S_1(x)$ from the one-dimensional marginals
-- statement:
--   For a random vector $\xi:\Omega\to\mathbb R^r$, $r\ge1$, on a probability space and $x\in\mathbb R^r$,
--   $$
--   S_1(x)=\sum_{i=1}^r\mathbb P(B_i(x))=r-\sum_{i=1}^r\mathbb P(A_i(x))=r-\sum_{i=1}^rF_i(x_i).
--   $$
--   So the first binomial moment needs only the one-dimensional marginal distributions.
--
--   Differences from the source:
--   - encoding: events $B_1,\dots,B_r$ (or variables $v_1,\dots,v_r$) indexed by $1,\dots,r$ → indexed by `Fin r`, that is by $0,\dots,r-1$; reason: Lean convention; same instances
--   - encoding: the number $r$ of events $B_1,\dots,B_r$ (the dimension of $\xi$ with values in $\mathbb R^r$) is left implicit → hypothesis `1 ≤ r`; reason: the family $B_1,\dots,B_r$ starts at $B_1$, so the book has $r\ge1$; the hypothesis excludes only the empty family
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, p.289 (PDF 298)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_lowerEvent
import Definitions.Def_KallMayerSLP_Bonferroni_exceedanceEvent
import Definitions.Def_KallMayerSLP_Bonferroni_marginalCDF

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- `S₁(x) = ∑_i ℙ(B_i(x)) = r - ∑_i ℙ(A_i(x)) = r - ∑_i F_i(x_i)`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, §3.4, p.289 (PDF 298). -/
theorem binomial_moment_one_marginals {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (ξ : Ω → Fin r → ℝ) (hξ : Measurable ξ) (x : Fin r → ℝ) :
    binomialMoment μ (exceedanceEvent ξ x) 1 = ∑ i, μ.real (exceedanceEvent ξ x i) ∧
    ∑ i, μ.real (exceedanceEvent ξ x i) = (r : ℝ) - ∑ i, μ.real (lowerEvent ξ x i) ∧
    (r : ℝ) - ∑ i, μ.real (lowerEvent ξ x i) = (r : ℝ) - ∑ i, marginalCDF μ ξ i (x i) := by sorry

end KallMayerSLP.Bonferroni
