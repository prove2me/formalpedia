-- Prove2me | Theorems.Thm_MeasureTheory_radial_majorant_exterior_bound
-- name    : MeasureTheory.radial_majorant_exterior_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T17:07:08.01416+00:00
-- url     : https://prove2.me/theorems/bf507f9b-feec-42bd-8d6e-c78e41bbf87a
-- title:
--   Integrated exterior bound for the Holder far-field majorant
-- statement:
--   Let $n\ge1$, $\alpha<1$, $\delta>0$, and let $F:\mathbb R^n\to\mathbb R$ be Lebesgue measurable up to null sets. For real constants $C,H$, suppose
--
--   $$|F(z)|\le CH\delta\|z\|^{\alpha-n-1}\quad(\|z\|>\delta).$$
--
--   Then $F$ is integrable outside the closed ball of radius $\delta$, and
--
--   $$\left|\int_{\|z\|>\delta}F(z)\,dz\right|\le\frac{n|B_1(0)|CH}{1-\alpha}\delta^\alpha.$$
--
--   The majorization hypothesis already forces $CH\ge0$; no separate sign assumptions are needed. This isolates the integration step after the pointwise kernel difference bound.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed p. 42, Theorem 2.28 proof, part (b1). General measurable-majorant formulation of the exterior integration step.

import Theorems.Thm_MeasureTheory_integral_norm_rpow_exterior
import Mathlib.Tactic.Ring

open MeasureTheory Metric
set_option autoImplicit false

theorem MeasureTheory.radial_majorant_exterior_bound (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : α < 1)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hm : AEStronglyMeasurable F volume)
    (C H δ : ℝ) (hδ : 0 < δ)
    (hb : ∀ z, δ < ‖z‖ → ‖F z‖ ≤ C * H * δ * ‖z‖ ^ (α - n - 1)) :
    IntegrableOn F (closedBall 0 δ)ᶜ ∧
      |∫ z in (closedBall 0 δ)ᶜ, F z| ≤
        (n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
          C * H * δ ^ α / (1 - α) := by sorry
