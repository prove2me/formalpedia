-- Prove2me | Theorems.Thm_NewtonCartan_contDiff_integral_I01
-- name    : NewtonCartan.contDiff_integral_I01
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:08:29.281222+00:00
-- url     : https://prove2.me/theorems/a2a1196b-235c-4b91-aa78-65d2715323e7
-- title:
--   ContDiff of a parameter-dependent interval integral on $[0,1]$
-- statement:
--   Let $E$ be a finite-dimensional real normed space. If a function $g : E \times \mathbb{R} \to \mathbb{R}$ is of class $C^n$ (for $n \in \mathbb{N}\cup\{\infty\}$), then the parameter-dependent integral
--   $$
--   x \mapsto \int_0^1 g(x,s)\,ds
--   $$
--   is likewise of class $C^n$ as a map $E \to \mathbb{R}$.
--
--   This is the standard differentiation-under-the-integral statement for continuous dependence of the integrand on the parameter, specialized to the compact interval $[0,1]$ and used as a building block for ContDiff assembly of radial Poincaré potentials.
-- source:
--   Standard fact from multivariable calculus / Mathlib ParametricIntervalIntegral; needed for Trautman recovery (Newton–Cartan Prop. 2.2) spatial potential assembly

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

open scoped ContDiff Topology Interval
open MeasureTheory Metric Set Filter ContinuousLinearMap

namespace NewtonCartan

theorem contDiff_integral_I01 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (n : ℕ∞) (g : E → ℝ → ℝ)
    (hg : ContDiff ℝ n (fun p : E × ℝ => g p.1 p.2)) :
    ContDiff ℝ n (fun x : E => ∫ s in (0 : ℝ)..1, g x s) := by sorry

end NewtonCartan
