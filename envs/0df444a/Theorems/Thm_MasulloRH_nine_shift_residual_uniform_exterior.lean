-- Prove2me | Theorems.Thm_MasulloRH_nine_shift_residual_uniform_exterior
-- name    : MasulloRH.nine_shift_residual_uniform_exterior
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T21:37:41.169463+00:00
-- url     : https://prove2.me/theorems/9a407d2d-748e-4bed-b582-9d9f0e66c646
-- title:
--   Uniform exterior energy bound for the nine rational theta translates
-- statement:
--   For every endpoint weight with c-b at least 1/2 and c+b at most 1, the weighted squared residual of the nine theta translates is integrable. The integral outside [-6,6] is at most 1/1000000. This includes the limiting weight.
-- source:
--   Masullo fixed-Gaussian approximation route. The witness uses the mission theta function, rational interval arithmetic and the published finite theta truncation. The energy estimate is unconditional. https://prove2.me/theorems/4fc48a8d-7b85-5f54-883e-2b08fff585f7 https://prove2.me/theorems/2e9c99f7-cd06-43f7-a85b-f4d2cc422151 https://prove2.me/theorems/2d121368-d18c-484d-9ad7-8213e62d8b2d

import Definitions.Def_MasulloRH_NineShiftWindows
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta

open MeasureTheory Set MasulloRH MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest MasulloRH.NineShift

theorem MasulloRH.nine_shift_residual_uniform_exterior (c b : ℝ) (hl : 1/2 ≤ c-b) (hr : c+b ≤ 1) :
    Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|) * ‖err x‖^2) ∧
    energy c b err - (∫ x : ℝ in Icc (-6) 6, Real.exp (2*c*x+2*b*|x|)*‖err x‖^2)
      ≤ 1/1000000 := by sorry
