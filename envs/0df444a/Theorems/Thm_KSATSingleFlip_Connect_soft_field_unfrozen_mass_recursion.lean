-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_unfrozen_mass_recursion
-- name    : KSATSingleFlip.Connect.soft_field_unfrozen_mass_recursion
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:51:24.264045+00:00
-- url     : https://prove2.me/theorems/e6548f7d-d40d-4777-b0bd-a999ac3bb4f0
-- title:
--   Exact unfrozen-mass recursion for the soft-field update
-- statement:
--   For β ≥ 0 and a symmetric finite measure ν with finite cosh integral, the soft-field update satisfies u(Rβν)=β exp(u(ν)), where u(ν)=∫cosh(z)ν(dz). The conclusion is expressed as an extended-nonnegative integral and an exact real exponential. This is the unfrozen-mass identity printed alongside equation (4.3).
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and equation (4.3), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
open MeasureTheory ProbabilityTheory KSATSingleFlip.Connect
open scoped ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_field_unfrozen_mass_recursion (ν : Measure ℝ) [IsFiniteMeasure ν] (β : ℝ) (hβ : 0 ≤ β)
    (hsym : Measure.map (fun z : ℝ => -z) ν = ν) (hcosh : Integrable Real.cosh ν) :
    (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂(Rbeta β ν)) =
      ENNReal.ofReal (β*Real.exp (∫ z, Real.cosh z ∂ν)) := by sorry
