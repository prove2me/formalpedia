-- Prove2me | Theorems.Thm_MasulloRH_moving_spatial_cutoffs_lose_translated_critical_mass
-- name    : MasulloRH.moving_spatial_cutoffs_lose_translated_critical_mass
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T07:08:15.539798+00:00
-- url     : https://prove2.me/theorems/ff39b25c-c8df-41c3-9c6e-0d6b05c07072
-- title:
--   Moving spatial cutoffs lose arithmetic-scale mass in the actual critical-width Hilbert space
-- statement:
--   Write L_n=R_n+d_n with R_n,d_n nonnegative, and w(x)=exp(|x|)(1+x²)². If d_n tends to infinity and exp(-d_n)(1+R_n²)/(1+d_n²) is uniformly bounded, then the translated Gram integral supported on |x|≤R_n and divided by exp(L_n) tends to zero for every fixed profile g integrable against w. In particular all fixed Hilbert vectors have normalized squared norm tending to zero after this moving cutoff and translation.
-- source:
--   Masullo (9.2.2.41); critical-width large-translation asymptotics for the global Gram form.

import Mathlib
open Filter Topology MeasureTheory

theorem MasulloRH.moving_spatial_cutoffs_lose_translated_critical_mass (R d : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) (hd : ∀ n, 0 ≤ d n)
    (hes : Tendsto d atTop atTop) (C : ℝ) (hC : ∀ n,
      Real.exp (-d n) * (1+(R n)^2)/(1+(d n)^2) ≤ C)
    (g : ℝ → ℝ) (hg : AEStronglyMeasurable g volume)
    (hint : Integrable (fun y : ℝ => (Real.exp |y| * (1+y^2)^2) * |g y|)) :
    Tendsto (fun n => ∫ y : ℝ, if |y+(R n+d n)| ≤ R n then
      ((Real.exp |y+(R n+d n)| * (1+(y+(R n+d n))^2)^2) / Real.exp (R n+d n)) * g y
      else 0) atTop (𝓝 0) := by sorry
