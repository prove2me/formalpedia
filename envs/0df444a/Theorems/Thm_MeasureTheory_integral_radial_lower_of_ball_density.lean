-- Prove2me | Theorems.Thm_MeasureTheory_integral_radial_lower_of_ball_density
-- name    : MeasureTheory.integral_radial_lower_of_ball_density
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T21:26:29.280268+00:00
-- url     : https://prove2.me/theorems/cbd4fb22-4e5e-4076-ba0e-3f49bc7c91f3
-- title:
--   Lower integral bound from symmetric-ball density
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb R$, $t\in\mathbb R$, $\delta>0$, and $c\ge0$. Suppose
--
--   $$\mu((t-r,t+r))/(2r)\ge c\qquad(0<r<\delta).$$
--
--   For every continuous function $f:\mathbb R\to\mathbb R$ that is nonnegative and nonincreasing on $[0,\infty)$,
--
--   $$2c\int_0^\delta f(r)\,dr\le\int_{\mathbb R}f(|x-t|)\,d\mu(x).$$
--
--   The radial integrand is bounded by $f(0)$ and therefore integrable. This comparison applies to arbitrary decreasing radial kernels, including Poisson kernels. A proof can use the layer-cake formula and domination of centered-ball masses, extending the strict-radius assumption to the cutoff by continuity from below. This is an open prerequisite, rather than a proved consequence of the proposed Poisson reduction.
-- source:
--   Generalization of the radial mass comparison in G. Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99 (2009), p. 109, proof of Theorem 3.22, following Eq. (3.90). https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf (PDF p. 120). Layer-cake route: Mathlib/MeasureTheory/Integral/Layercake.lean, lintegral_eq_lintegral_meas_lt. The general-kernel statement is an auxiliary extension, not a verbatim theorem in Teschl.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set
open scoped ENNReal

theorem MeasureTheory.integral_radial_lower_of_ball_density
    (μ : Measure ℝ) [IsFiniteMeasure μ] (t δ c : ℝ)
    (hδ : 0 < δ) (hc : 0 ≤ c) (f : ℝ → ℝ)
    (hf : Continuous f) (hnonneg : ∀ r ∈ Ici (0 : ℝ), 0 ≤ f r)
    (hmono : AntitoneOn f (Ici (0 : ℝ)))
    (hdensity : ∀ r : ℝ, 0 < r → r < δ →
      ENNReal.ofReal c ≤ μ (Metric.ball t r) / volume (Metric.ball t r)) :
    2 * c * (∫ r : ℝ in 0..δ, f r) ≤ ∫ x : ℝ, f |x - t| ∂μ := by sorry
