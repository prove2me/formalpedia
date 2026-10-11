-- Prove2me | Theorems.Thm_MeasureTheory_integral_norm_rpow_ball
-- name    : MeasureTheory.integral_norm_rpow_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T16:51:14.482051+00:00
-- url     : https://prove2.me/theorems/8f0e887c-bf01-454e-bf7e-360a5c18f025
-- title:
--   Exact radial power integral on a Euclidean ball
-- statement:
--   For an integer $n\ge1$, a real exponent $\alpha>0$ and a radius $R>0$, the function $z\mapsto\|z\|^{\alpha-n}$ is Lebesgue integrable on $B_R(0)\subset\mathbb R^n$, and
--
--   $$\int_{B_R(0)}\|z\|^{\alpha-n}\,dz=\frac{n|B_1(0)|}{\alpha}R^\alpha.$$
--
--   The statement includes the origin with the total real-power convention; a singleton has zero Lebesgue measure. This is the radial integral used in the near-singularity estimate.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed p. 41, Theorem 2.28 proof, part (a). Explicit polar-coordinate evaluation of the radial majorant used there.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Metric
set_option autoImplicit false

theorem MeasureTheory.integral_norm_rpow_ball (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α)
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ (α - n)) (ball 0 R) ∧
      (∫ z : EuclideanSpace ℝ (Fin n) in ball 0 R, ‖z‖ ^ (α - n)) =
        (n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * R ^ α / α := by sorry
