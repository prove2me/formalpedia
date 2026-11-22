-- Prove2me | Theorems.Thm_MasulloRH_weighted_log_line_convolution_riesz_vector_detected_by_theta_translates
-- name    : MasulloRH.weighted_log_line_convolution_riesz_vector_detected_by_theta_translates
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T05:26:19.968685+00:00
-- url     : https://prove2.me/theorems/c41ecb7a-f625-45ce-899f-5ddd57671c4a
-- title:
--   Every nonzero compact radial convolution of the weighted Riesz profile is detected by a translated packet
-- statement:
--   For $w(x)=e^{2\alpha |x|}(1+x^2)^2$, $\alpha\ge 0$, let $h$ be nonzero continuous of compact support on the real log-norm line, and $u$ be nonzero continuous with $\int |u(x)|e^{t|x|}dx<\infty$ for every real $t$. Then the bounded function $w(x)(h*(1/w))(x)$ has nonzero Haar inner product against some translate of $u$. This detects off-diagonal geometric/spectral leakage at width zero and at critical width on the rational radial component when applied to a theta packet and a zeta-zero Riesz vector.
-- source:
--   Masullo (9.1.2.3), (9.2.2.41), (10.4.1.1), (11.2.1.4). Fourier uniqueness, Plancherel, and analyticity of Fourier transforms with exponential moments.

import Mathlib
open MeasureTheory

theorem MasulloRH.weighted_log_line_convolution_riesz_vector_detected_by_theta_translates
    (α : ℝ) (hα : 0 ≤ α)
    (h u : ℝ → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h)
    (hh0 : h ≠ 0) (hu : Continuous u) (hu0 : u ≠ 0)
    (hdec : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * |x|) * ‖u x‖)) :
    let w : ℝ → ℝ := fun x : ℝ => Real.exp (2 * α * |x|) * (1 + x^2)^2
    let b : ℝ → ℂ := fun x : ℝ => (w x : ℂ) * ∫ y : ℝ, h y / (w (x-y) : ℂ)
    ∃ c : ℝ, (∫ x : ℝ, b x * (starRingEnd ℂ) (u (x-c))) ≠ 0 := by sorry
