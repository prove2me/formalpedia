-- Prove2me | Theorems.Thm_GaussianMatrix_density_integral_le_tail_bound
-- name    : GaussianMatrix.density_integral_le_tail_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-19T19:52:46.180447+00:00
-- url     : https://prove2.me/theorems/fbf09435-ab79-412b-a898-5e1c626da6c5
-- title:
--   Closed-form upper bound for the integrated Wishart density majorant
-- statement:
--   Let 1 ≤ r ≤ k and t > 0. The integrated Edelman's density majorant c_{r,k} λ^{(k-r-1)/2} e^{-λ/2} over (0, t] is at most Γ(k-r+2)^{-1} (t(k+r)/2)^{(k-r+1)/2}. This is the purely analytic computation behind Tropp-Webber (B.7): it combines the power-exponential integral bound with the two-sided Gamma ratio bound, and isolates every non-probabilistic step of the Wishart lower-tail estimate.
-- source:
--   Analytic core of the Wishart lambda-min lower tail (Tropp-Webber B.7) used by Gaussian Random Matrices II: integrates the pointwise density majorant via integral_power_exp_le and tw_gamma_ratio_bound, leaving only the joint-eigenvalue density bound (the mission root) open.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix
open GaussianMatrix

theorem GaussianMatrix.density_integral_le_tail_bound {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal
      (2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
        / (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))
        * x ^ (((k : ℝ) - r - 1) / 2) * Real.exp (-x / 2))
      ≤ ENNReal.ofReal ((1 / Real.Gamma ((k : ℝ) - r + 2))
        * (t * ((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)) := by
  sorry
