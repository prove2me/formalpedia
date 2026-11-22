-- Prove2me | Theorems.Thm_MasulloRH_negative_period_fourier_idempotent_weighted_high_tail
-- name    : MasulloRH.negative_period_fourier_idempotent_weighted_high_tail
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T14:43:21.060197+00:00
-- url     : https://prove2.me/theorems/b0dd2225-6299-4f09-9e09-51c6b54140b1
-- title:
--   Negative-period Fourier coefficient norm and explicit two-sided high-frequency tail in the critical weighted metric
-- statement:
--   For lattice spacing delta=2 pi/L, an E-valued negative-period Fourier average of a row bounded by C(1+abs(t))^2 has norm at most C(1+L)^2. For a scalar profile bounded by D/(1+abs(u))^(r+2), the two signs of frequencies A+k delta have absolutely summable weighted coefficients and total norm at most 2DC(1+L)^2 (1+delta)/(delta (1+A)^(r+1)). The theorem also proves the exact pointwise critical physical weight ratio bound producing the negative-period row estimate. For a circle representation the averages at lattice points give its individual spectral idempotents. E may carry a chosen complex norm.
-- source:
--   Masullo mission, weighted global critical Hilbert space, removing a growing global frequency band after controlling finite bands. The period is sampled on its negative translate to avoid exponential growth.

import Mathlib
open MeasureTheory Set Real
open scoped Interval

theorem MasulloRH.negative_period_fourier_idempotent_weighted_high_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (L A C D : ℝ) (hL : 0 < L) (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (r : ℕ) (V : ℝ → E) (m : ℝ → ℂ)
    (hV : ∀ t ∈ Icc (-L) 0, ‖V t‖ ≤ C*(1+|t|)^2)
    (hm : ∀ u, ‖m u‖ ≤ D/(1+|u|)^(r+2)) :
    let δ := 2*Real.pi/L
    let P := fun u : ℝ => (L⁻¹ : ℂ) • (∫ t in (-L)..0, Complex.exp (((-u*t : ℝ):ℂ)*Complex.I) • V t)
    let u := fun k : ℕ => A + k*δ
    let z := fun k : ℕ => ‖m (u k) • P (u k)‖ + ‖m (-(u k)) • P (-(u k))‖
    (∀ x t : ℝ, t ≤ 0 → exp (t+|x+t|-|x|)*(1+(x+t)^2)^2 ≤ (1+|t|)^4*(1+x^2)^2) ∧
    (∀ v, ‖P v‖ ≤ C*(1+L)^2) ∧ Summable z ∧
    (∑' k, z k) ≤ 2*D*C*(1+L)^2 * (1+δ)/(δ*(1+A)^(r+1)) := by sorry
