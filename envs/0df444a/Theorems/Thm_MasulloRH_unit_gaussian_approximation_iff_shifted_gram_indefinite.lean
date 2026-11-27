-- Prove2me | Theorems.Thm_MasulloRH_unit_gaussian_approximation_iff_shifted_gram_indefinite
-- name    : MasulloRH.unit_gaussian_approximation_iff_shifted_gram_indefinite
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T22:26:22.041964+00:00
-- url     : https://prove2.me/theorems/481eef6a-5bed-4ec3-8e5f-f6dabdfce704
-- title:
--   A shifted Gram matrix detects finite Gaussian approximation at any tolerance
-- statement:
--   For any window strictly inside the critical strip, any finite list of rational shifts and any real tolerance, a rational complex coefficient vector has squared error below tolerance exactly when the shifted real Gram matrix fails to be positive semidefinite.
-- source:
--   Masullo RH specialization, fixed unit Gaussian in the expanding weighted windows. The dyadic theta Mellin identity and the accepted finite-window energy identities are used at their registered types. https://prove2.me/theorems/8481aa5d-a121-4938-8de2-17c814da37b2

import Definitions.Def_MasulloRH_RationalThetaGrid

open MeasureTheory MasulloRH MasulloRH.RationalThetaGrid MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest

theorem MasulloRH.unit_gaussian_approximation_iff_shifted_gram_indefinite (c b τ : ℝ) (hl : 0 < c-b) (hr : c+b < 1) (m : ℕ) (y : Fin m → ℚ) :
    (∃ a : Fin m → ℚ × ℚ, energy c b (residual 0 (fun i => asComplex (a i)) (fun i => (y i:ℝ))) < τ) ↔
      ¬ (gram c b y - Matrix.single 0 0 τ).PosSemidef := by sorry
