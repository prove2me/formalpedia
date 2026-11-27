-- Prove2me | Theorems.Thm_MasulloRH_quarter_shift_gaussian_central_energy
-- name    : MasulloRH.quarter_shift_gaussian_central_energy
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T23:57:31.295239+00:00
-- url     : https://prove2.me/theorems/f5e721d8-55f9-56cf-be9d-7249556cb318
-- title:
--   Central energy of 25 quarter-spaced theta translates
-- statement:
--   On [−7,7], the weighted squared residual of the 25 rational translates integrates to at most 31/10¹² for all c,b with c−b≥1/2 and c+b≤1, given integrability.
-- source:
--   Masullo RH specialization, finite Gaussian approximations on all expanding weighted windows. The signed residual and the shifted Gram matrices use the mission’s published definitions. The previous factorial-grid proof is https://prove2.me/submissions/770071af-0aae-4bf3-ad37-8d6f2536bd14 .

import Definitions.Def_MasulloRH_ThetaDerivativeCertificates

open MeasureTheory Set MasulloRH MasulloRH.ThetaDerivativeCertificate MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest MasulloRH.CentralInterval MasulloRH.InteriorEvaluator

theorem MasulloRH.quarter_shift_gaussian_central_energy (c b : ℝ) (hl : 1/2 ≤ c-b) (hr : c+b ≤ 1)
    (hi : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖err x‖^2)) :
    (∫ x : ℝ in Icc (-7) 7, Real.exp (2*c*x+2*b*|x|)*‖err x‖^2) ≤ 31/1000000000000 := by sorry
