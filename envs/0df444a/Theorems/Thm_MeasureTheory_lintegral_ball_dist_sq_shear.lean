-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_ball_dist_sq_shear
-- name    : MeasureTheory.lintegral_ball_dist_sq_shear
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T09:25:24.469673+00:00
-- url     : https://prove2.me/theorems/fc16ab5b-c470-4222-b389-00c651ca4244
-- title:
--   Reorganizing a nearby-pairs double integral by the increment vector
-- statement:
--   Let $B\subseteq\mathbb C$ be open, let $f$ be continuous on $B$ with values in a metric space, and let $\varepsilon\in\mathbb R$. Then the double integral of the squared increment over nearby pairs of points of $B$ can be reorganized by the increment vector:
--   $$\int_{B}\!\!\int_{B\cap B_\varepsilon(z)} d\bigl(f(w),f(z)\bigr)^{2}\,dw\,dz\;=\;\int_{B_\varepsilon(0)}\!\!\int_{B\cap(B-h)} d\bigl(f(z+h),f(z)\bigr)^{2}\,dz\,dh .$$
--
--   **Role.** The left-hand side is the shape in which the Korevaar--Schoen approximate energy at scale $\varepsilon$ is defined: an average, over base points $z$, of the squared increments to all points within $\varepsilon$. The right-hand side is the shape in which lower bounds are proved: for a *fixed* increment $h$ the inner integral compares $f$ with its translate by $h$, and chains of the form $z,\,z+h,\dots,z+nh$ can be run inside it. Passing between the two is the change of variables $w=z+h$ followed by Fubini--Tonelli, and this lemma records it once and for all.
--
--   **Formalization note.** No measurability of $f$ off $B$ is assumed, and none is needed: both sides only ever see $f$ at points of $B$. Concretely, the integrand is the indicator of the open set $\{(z,h): z\in B,\ z+h\in B,\ \lVert h\rVert<\varepsilon\}$ times a function continuous there, which is enough for Tonelli; the two iterated integrals are then identified with the two sides by translation invariance of Lebesgue measure on $\mathbb C$.
-- source:
--   The change of variables underlying the Poincare inequality for the Korevaar--Schoen approximate energies, N. Korevaar and R. Schoen, Sobolev spaces and harmonic maps for metric space targets, Comm. Anal. Geom. 1 (1993), Section 1.

import Mathlib

namespace MeasureTheory

open MeasureTheory

universe u

theorem lintegral_ball_dist_sq_shear {X : Type u} [PseudoMetricSpace X]
    (B : Set ℂ) (hB : IsOpen B) (f : ℂ → X) (hf : ContinuousOn f B) (eps : ℝ) :
    (∫⁻ z in B, ∫⁻ w in B ∩ Metric.ball z eps,
        ENNReal.ofReal (dist (f w) (f z) ^ 2))
      = ∫⁻ h in Metric.ball (0:ℂ) eps,
          ∫⁻ z in B ∩ (fun y : ℂ => y + h) ⁻¹' B,
            ENNReal.ofReal (dist (f (z + h)) (f z) ^ 2) := by sorry

end MeasureTheory
