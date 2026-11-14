-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_clause_intensity_integral
-- name    : KSATSingleFlip.Connect.soft_clause_intensity_integral
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:40:08.179482+00:00
-- url     : https://prove2.me/theorems/cb499402-ae54-4cb8-b3fd-49e357790fda
-- title:
--   Clause-intensity integrals equal weighted soft-field pairings
-- statement:
--   For a test continuous on [0,1], its integral against the paper’s clause-parameter intensity ρν equals four times the corresponding weighted soft-field pairing with q↦f(1−q). The indicator gives a canonical measurable extension outside [0,1], while the intensity is supported there.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, equation (4.3) and proof of Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldClauseIntensity
import Mathlib
open MeasureTheory KSATSingleFlip.Connect Set
open scoped ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_clause_intensity_integral (ν : Measure ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) :
    (∫ s, (Icc 0 1).indicator f s ∂(softClauseIntensity ν)) =
      4*pairing (fun q => f (1-q)) ν := by sorry
