-- Prove2me | Theorems.Thm_MasulloRH_exact_laplace_energy_bound_on_window
-- name    : MasulloRH.exact_laplace_energy_bound_on_window
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T19:23:28.247395+00:00
-- url     : https://prove2.me/theorems/32586269-e0b7-55c1-894d-f155eaf9b460
-- title:
--   An explicit squared Laplace evaluation bound in a shifted exponential window
-- statement:
--   Inside a window of center c and width b, the squared norm of the Laplace evaluation is at most the weighted squared energy times the sum of the reciprocals of twice the two distances from the vertical edges.
-- source:
--   Developed for the Masullo theta-window argument and the centered Möbius target. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 The proof adapts the work in https://prove2.me/submissions/5b2cbfbc-22d8-4073-bb0e-dbecd2699cb3 and uses the weighted Mellin evaluation https://prove2.me/theorems/e2170362-8fa5-4c24-b4ab-c9ae6809338e .

import Definitions.Def_MasulloRH_GaussianThetaApproximation

open MasulloRH.GaussianApproximation MeasureTheory

theorem MasulloRH.exact_laplace_energy_bound_on_window (f : ℝ → ℂ) (c b : ℝ) (s : ℂ) (hs : |s.re-c|<b)
    (hi : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖f x‖^2)) :
    ‖∫ x : ℝ, Complex.exp (s*x)*f x‖^2 ≤ energy c b f *
      (1/(2*(b-(s.re-c))) + 1/(2*(b+(s.re-c)))) := by sorry
