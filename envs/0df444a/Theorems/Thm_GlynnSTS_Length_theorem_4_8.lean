-- Prove2me | Theorems.Thm_GlynnSTS_Length_theorem_4_8
-- name    : GlynnSTS.Length.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:59.358979+00:00
-- url     : https://prove2.me/theorems/6c8a444b-a516-40c1-8148-a8cf9cc2d3d5
-- title:
--   Theorem 4.8 — lower bound on the expected-scale criterion
-- statement:
--   Let $B$ be standard Brownian motion, $g\in\mathcal M$, and $0<\delta<1$. Let $z$ satisfy $H(z)=1-\delta/2$, and let $p$ satisfy $\Phi(p)=1-\delta/2$ for the standard normal distribution function $\Phi$. Then
--   $$
--   E[g(B)]\,z\ge p=\Phi^{-1}(1-\delta/2).
--   $$
--   This is the distributional lower bound that controls every STS interval's asymptotic expected width.
--
--   **Formalization Note** The expectation is an extended nonnegative integral; the normal and STS quantiles are specified by equations, avoiding an infimum default value.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 10, Theorem 4.8; proof pp. 11–12

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Length

/-- Theorem 4.8, p. 10: the expected Brownian scale times its upper quantile is at least the normal quantile. -/
theorem theorem_4_8 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (z : ℝ) (hz : H P B g z = 1 - δ / 2)
    (p : ℝ) (hp : cdf (gaussianReal 0 1) p = 1 - δ / 2) :
    ENNReal.ofReal p ≤
      (∫⁻ ω, ENNReal.ofReal (g (B ω)) ∂P) * ENNReal.ofReal z := by sorry

end GlynnSTS.Length
