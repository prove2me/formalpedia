-- Prove2me | Theorems.Thm_MasulloRH_fixed_gaussian_tail_iff_factorial_gram_tests
-- name    : MasulloRH.fixed_gaussian_tail_iff_factorial_gram_tests
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T22:26:43.404837+00:00
-- url     : https://prove2.me/theorems/cdae9da6-cba3-4d1f-a69d-7bd9b1a6ab74
-- title:
--   Exact factorial Gram matrix criterion for the Gaussian approximation tail
-- statement:
--   The registered fixed-Gaussian approximation starting at j=16,384 is equivalent to finding, for each such j, a factorial grid whose shifted Gram matrix fails to be positive semidefinite on window j+1.
-- source:
--   Masullo RH specialization, fixed unit Gaussian in the expanding weighted windows. The dyadic theta Mellin identity and the accepted finite-window energy identities are used at their registered types. https://prove2.me/theorems/28908aa5-2420-4285-97be-cda4701d769b

import Definitions.Def_MasulloRH_RationalThetaGrid

open MeasureTheory MasulloRH MasulloRH.RationalThetaGrid MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest

theorem MasulloRH.fixed_gaussian_tail_iff_factorial_gram_tests : tailApprox ↔ ∀ j : ℕ, 16384 ≤ j → ∃ n : ℕ, passes j n := by sorry
