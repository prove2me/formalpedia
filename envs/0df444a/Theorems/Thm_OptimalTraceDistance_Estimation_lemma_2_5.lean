-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_lemma_2_5
-- name    : OptimalTraceDistance.Estimation.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:44:45.653572+00:00
-- url     : https://prove2.me/theorems/c3c10dad-a0bb-4888-9629-e419a78765bf
-- title:
--   Lemma 2.5 — polynomial filter
-- statement:
--   For every $0<b\le1$, the actual polynomial $R_b$ in (9) satisfies
--   $$\deg R_b\le b^{-1/2},\quad R_b(0)=1,\quad 0\le R_b(x)\le1,\quad xR_b(x)^2\le2^7b\quad(0\le x\le1).$$
--   On $0\le x\le b$, it is positive and
--   $$-\log R_b(x)\le(x/b)^2.$$
--   The definition uses its polynomial value at zero and the constant branch at $b=1/32$.
--
--   Differences from the source:
--   - encoding: The logarithmic bound for 0≤x≤b → Positivity of R_b(x) is included in that conclusion; reason: The source proof p.26 gives positivity; it establishes the domain of the real logarithm rather than imposing a new input hypothesis
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Lemma 2.5, p. 8.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem lemma_2_5 (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
  ((filter b).natDegree : ℝ) ≤ b ^ (-(1/2 : ℝ)) ∧ (filter b).eval 0 = 1 ∧
  (∀ x ∈ Set.Icc (0 : ℝ) 1,
    0 ≤ (filter b).eval x ∧ (filter b).eval x ≤ 1 ∧
    x*((filter b).eval x)^2 ≤ (2 : ℝ)^7*b) ∧
  (∀ x ∈ Set.Icc (0 : ℝ) b,
    0 < (filter b).eval x ∧ -Real.log ((filter b).eval x) ≤ (x/b)^2) := by sorry

end OptimalTraceDistance.Estimation
