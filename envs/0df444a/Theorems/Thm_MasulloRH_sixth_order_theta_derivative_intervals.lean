-- Prove2me | Theorems.Thm_MasulloRH_sixth_order_theta_derivative_intervals
-- name    : MasulloRH.sixth_order_theta_derivative_intervals
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T23:55:39.549832+00:00
-- url     : https://prove2.me/theorems/64c80f3f-38f3-5822-b358-eb491ef2945a
-- title:
--   Real theta-series truncations through six derivatives and a certified tail
-- statement:
--   The six-term direct and reflected theta truncations have successive derivatives given by explicit polynomials through order six. Rational intervals enclose each derived expression, and a geometric tail controls its difference from the true theta function at order zero.
-- source:
--   Masullo RH specialization, finite Gaussian approximations on all expanding weighted windows. The signed residual and the shifted Gram matrices use the mission’s published definitions. The previous factorial-grid proof is https://prove2.me/submissions/770071af-0aae-4bf3-ad37-8d6f2536bd14 . Uses the exact dyadic theta reflection and six-term truncation, https://prove2.me/theorems/8632ce84-3f47-4ac8-b2ff-ae87b3a5a9fe and https://prove2.me/theorems/2e9c99f7-cd06-43f7-a85b-f4d2cc422151 .

import Definitions.Def_MasulloRH_ThetaDerivativeCertificates

open MeasureTheory Set MasulloRH MasulloRH.ThetaDerivativeCertificate MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest MasulloRH.CentralInterval MasulloRH.InteriorEvaluator

theorem MasulloRH.sixth_order_theta_derivative_intervals :
    (∀ (b : Bool) (n : ℕ), n < 6 → ∀ x : ℝ, HasDerivAt (tJet b n) (tJet b (n+1) x) x) ∧
    (∀ (b : Bool) (n : ℕ) (z : Box) (x : ℝ), Covers z x →
      Covers (thetaJB b n (params b z)) (tJet b n x)) ∧
    (∀ (b : Bool) (z : Box) (x : ℝ), Covers z x → 0 < tailDen (params b z) →
      ‖theta x-(tJet b 0 x:ℂ)‖ ≤ (tailU (params b z):ℝ)) := by sorry
