-- Prove2me | Theorems.Thm_MasulloRH_exponential_window_gaussian_mixture_gram_bound
-- name    : MasulloRH.exponential_window_gaussian_mixture_gram_bound
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T20:17:04.40854+00:00
-- url     : https://prove2.me/theorems/ebe5e57b-f29f-4c28-8c35-7d51e2bbd49b
-- title:
--   A Gaussian overlap matrix bounds the energy on exponential windows
-- statement:
--   For a finite signed real combination of shifted normalized Gaussians of arbitrary positive inverse widths, the squared error is integrable for every indicated weight. Its integral is bounded by a signed double sum of explicit Gaussian overlaps whenever the left endpoint is at least one half and the right endpoint is at most one.
-- source:
--   Finite approximation for the Masullo fixed-Gaussian criterion on expanding windows. https://prove2.me/theorems/5b5a3819-6fdf-5ee5-ba13-5cfaec0d1147

import Definitions.Def_MasulloRH_GaussianMixtureWindows

open MeasureTheory Real MasulloRH MasulloRH.GaussianMixture MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest

theorem MasulloRH.exponential_window_gaussian_mixture_gram_bound {m : ℕ} (a p y : Fin m → ℝ) (hp : ∀ i, 0<p i) (c b : ℝ)
    (hl : 1/2 ≤ c-b) (hr : c+b ≤ 1) :
    let f := fun x : ℝ => ((∑ i, a i*bell (p i) (y i) x : ℝ) : ℂ)
    Integrable (fun x : ℝ => exp (2*c*x+2*b*|x|)*‖f x‖^2) ∧
    energy c b f ≤ ∑ i, ∑ j, a i*a j*(kernel (p i) (p j) (y i) (y j) 2 +
      (1/4)*kernel (p i) (p j) (y i) (y j) 0) := by sorry
