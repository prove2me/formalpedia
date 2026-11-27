-- Prove2me | Theorems.Thm_MasulloRH_real_residual_conjugate_frequency_gain
-- name    : MasulloRH.real_residual_conjugate_frequency_gain
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T01:14:29.191133+00:00
-- url     : https://prove2.me/theorems/48e8535f-bd87-4622-9eaa-6c07de755c94
-- title:
--   Conjugate frequencies sharpen the weighted Laplace bound for real residuals
-- statement:
--   For a real-valued residual in a two-sided exponential window, twice the squared modulus of a Laplace moment with nonzero ordinate is at most its weighted energy times the diagonal evaluation constant plus the reciprocal of the absolute ordinate, with both terms inside the multiplier.
-- source:
--   MasulloRH logarithmic Gaussian-theta approximation, using the public quarter-shift certificate. The parameter is the unshifted zeta variable.

import Definitions.Def_MasulloRH_WindowLaplaceGram

open MeasureTheory MasulloRH.WindowLaplaceGram MasulloRH.GaussianApproximation
open scoped ComplexConjugate

theorem MasulloRH.real_residual_conjugate_frequency_gain (c b : ℝ) (f : ℝ → ℂ) (s : ℂ) (hs : |s.re-c| < b) (ht : 0 < |s.im|)
    (hf : ∀ x, conj (f x) = f x)
    (hi : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖f x‖^2))
    (hm : Integrable (fun x : ℝ => Complex.exp (s*x)*f x)) :
    2 * ‖moment f s‖^2 ≤ energy c b f *
      (1/(2*(s.re-(c-b))) + 1/(2*((c+b)-s.re)) + 1/|s.im|) := by sorry
