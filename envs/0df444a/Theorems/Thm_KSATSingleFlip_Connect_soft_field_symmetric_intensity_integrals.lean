-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_symmetric_intensity_integrals
-- name    : KSATSingleFlip.Connect.soft_field_symmetric_intensity_integrals
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:47:33.169022+00:00
-- url     : https://prove2.me/theorems/5c1809c0-305d-43f5-958e-aa9049e8c8e3
-- title:
--   Intensity and exponential integrals for symmetric soft-field measures
-- statement:
--   If a finite soft-field measure is symmetric under z↦−z and has integrable cosh, then w and e^z are integrable, ∫w dν=∫cosh dν+h(ν)/2, and ∫e^z dν=∫cosh dν. These are the exact intensity identities needed in the Poisson tilting calculation.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and equation (4.3), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
open MeasureTheory KSATSingleFlip.Connect
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_field_symmetric_intensity_integrals (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hsym : Measure.map (fun z : ℝ => -z) ν = ν)
    (hcosh : Integrable Real.cosh ν) :
    Integrable wInt ν ∧ Integrable Real.exp ν ∧
    (∫ z, wInt z ∂ν) = (∫ z, Real.cosh z ∂ν) + hPot ν/2 ∧
    (∫ z, Real.exp z ∂ν) = ∫ z, Real.cosh z ∂ν := by sorry
