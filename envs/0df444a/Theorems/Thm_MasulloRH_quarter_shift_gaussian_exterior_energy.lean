-- Prove2me | Theorems.Thm_MasulloRH_quarter_shift_gaussian_exterior_energy
-- name    : MasulloRH.quarter_shift_gaussian_exterior_energy
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T23:57:53.314024+00:00
-- url     : https://prove2.me/theorems/13e6e0a1-542b-4cc4-9725-2390b5db7292
-- title:
--   Exterior energy of the 25 quarter-spaced theta translates
-- statement:
--   For c−b≥1/2 and c+b≤1, the weighted squared residual is integrable and the two tails outside [−7,7] have combined integral at most 1/10¹⁴.
-- source:
--   Masullo RH specialization, finite Gaussian approximations on all expanding weighted windows. The signed residual and the shifted Gram matrices use the mission’s published definitions. The previous factorial-grid proof is https://prove2.me/submissions/770071af-0aae-4bf3-ad37-8d6f2536bd14 .

import Definitions.Def_MasulloRH_ThetaDerivativeCertificates

open MeasureTheory Set MasulloRH MasulloRH.ThetaDerivativeCertificate MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest MasulloRH.CentralInterval MasulloRH.InteriorEvaluator

theorem MasulloRH.quarter_shift_gaussian_exterior_energy (c b : ℝ) (hl : 1/2 ≤ c-b) (hr : c+b ≤ 1) :
    Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|) * ‖err x‖^2) ∧
    energy c b err - (∫ x : ℝ in Icc (-7) 7, Real.exp (2*c*x+2*b*|x|)*‖err x‖^2)
      ≤ 1/100000000000000 := by sorry
