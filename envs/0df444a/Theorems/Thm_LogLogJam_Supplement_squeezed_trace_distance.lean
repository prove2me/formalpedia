-- Prove2me | Theorems.Thm_LogLogJam_Supplement_squeezed_trace_distance
-- name    : LogLogJam.Supplement.squeezed_trace_distance
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T19:14:39.253511+00:00
-- url     : https://prove2.me/theorems/adbf4e57-31d2-40dd-9359-72395387ded2
-- title:
--   Physical trace distance of two one-mode squeezed vacua
-- statement:
--   Any two physical centered one-mode squeezed states with parameters (r,θ) and (s,φ) have trace distance equal to the square root of one minus two divided by the square root of the determinant of the sum of their two full quadrature covariances.
-- source:
--   https://arxiv.org/abs/2607.12983; Lemmas 4.1, 4.6 and §8.3, Eq. (144).

import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Definitions.Def_BosonicLearn_traceDist
open LogLogJam Matrix
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal

namespace LogLogJam.Supplement
theorem squeezed_trace_distance (ρ σ : State (Occupation (Fin 1))) (r θ s φ : ℝ)
    (hρ : squeezedAt ρ r θ) (hσ : squeezedAt σ s φ) :
    BosonicLearn.traceDist ρ.coefficients σ.coefficients = ENNReal.ofReal
      (Real.sqrt (1-2/Real.sqrt (Vsq (Real.exp (2*r)) θ + Vsq (Real.exp (2*s)) φ).det)) := by sorry
end LogLogJam.Supplement
