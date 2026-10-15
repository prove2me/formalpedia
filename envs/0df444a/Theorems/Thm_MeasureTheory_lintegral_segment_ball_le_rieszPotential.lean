-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_segment_ball_le_rieszPotential
-- name    : MeasureTheory.lintegral_segment_ball_le_rieszPotential
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T07:19:59.110642+00:00
-- url     : https://prove2.me/theorems/2d06457d-cfe8-4108-b1e7-caf0c57aaba6
-- title:
--   Averaged radial segment integrals bounded by a local Riesz potential
-- statement:
--   Let $n\ge1$. There is a finite constant $C_n\ge0$ such that every measurable $g:\mathbb R^n\to[0,\infty]$, center $x$, and radius $r>0$ satisfy
--
--   $$\int_{B(x,r)}\|z-x\|\int_0^1 g(x+t(z-x))\,dt\,dz\le |B(x,r)|C_n\int_{B(x,r)}g(z)\|z-x\|^{1-n}\,dz.$$
--
--   This is the measure-theoretic averaging step in the centered oscillation argument. It applies to arbitrary nonnegative measurable data, without differentiability, integrability, or finiteness assumptions. Polar coordinates and Tonelli's theorem give the bound with $C_n=(n|B(0,1)|)^{-1}$. Values at the center and at segment endpoints do not affect the integrals.
--
--   **Formalization Note** The functions take values in the extended nonnegative reals. The segment parameter uses Lebesgue measure restricted to the closed unit interval. The kernel is represented by a real power followed by conversion to the extended nonnegative reals.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed pp. 68–69 (PDF pp. 74–75), proof of Theorem 3.36, equation (3.14). The polar-coordinate/Tonelli averaging calculation is stated for arbitrary measurable nonnegative data instead of the gradient length.

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory
set_option autoImplicit false

theorem MeasureTheory.lintegral_segment_ball_le_rieszPotential {n : ℕ} (hn : 0 < n) :
    ∃ C : NNReal, ∀ g : EuclideanSpace ℝ (Fin n) → ENNReal,
      Measurable g → ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ z in Metric.ball x r, ENNReal.ofReal ‖z - x‖ *
        (∫⁻ t in Set.Icc (0 : ℝ) 1, g (x + t • (z - x)))) ≤
        volume (Metric.ball x r) * (C : ENNReal) *
          (∫⁻ z in Metric.ball x r, g z *
            ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) := by sorry
