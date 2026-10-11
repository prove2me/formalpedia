-- Prove2me | Theorems.Thm_MeasureTheory_integral_norm_rpow_exterior
-- name    : MeasureTheory.integral_norm_rpow_exterior
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T17:00:54.452819+00:00
-- url     : https://prove2.me/theorems/d6599b94-302b-43fe-ae85-a0b743f6de00
-- title:
--   Exact radial power integral outside a Euclidean ball
-- statement:
--   For an integer $n\ge1$, an exponent $\beta<0$ and $R>0$, the function $z\mapsto\|z\|^{\beta-n}$ is Lebesgue integrable on the complement of the closed ball $\overline B_R(0)$ in $\mathbb R^n$, and
--
--   $$\int_{\|z\|>R}\|z\|^{\beta-n}\,dz=\frac{n|B_1(0)|}{-\beta}R^\beta.$$
--
--   Taking $\beta=\alpha-1$ gives the convergent radial majorant in the far part of a singular-integral Holder estimate.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed p. 42, Theorem 2.28 proof, part (b1). Explicit polar-coordinate evaluation of the exterior radial majorant.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Metric
set_option autoImplicit false

theorem MeasureTheory.integral_norm_rpow_exterior (n : ℕ) (hn : 1 ≤ n) (β : ℝ) (hβ : β < 0)
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ (β - n))
        (closedBall 0 R)ᶜ ∧
      (∫ z : EuclideanSpace ℝ (Fin n) in (closedBall 0 R)ᶜ, ‖z‖ ^ (β - n)) =
        (n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * R ^ β / (-β) := by sorry
