-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_jump_moments
-- name    : KSATSingleFlip.Connect.soft_field_jump_moments
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:49:05.020257+00:00
-- url     : https://prove2.me/theorems/28302505-dfc5-41b1-94cf-15eb5e3134eb
-- title:
--   Exact mass and exponential moments of the soft-field jump intensity
-- statement:
--   For a symmetric finite soft-field measure with integrable cosh, let u=∫cosh(z)ν(dz) and let μ be the jump intensity obtained by weighting by w and mapping by a. Then μ(ℝ)=u+h(ν)/2, ∫e^x μ(dx)=2u, and ∫e^{−x} μ(dx)=u, with the equalities represented in extended nonnegative reals. This is the exact moment calculation underlying Poisson tilting.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and equation (4.3), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_field_jump_moments (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hsym : Measure.map (fun z : ℝ => -z) ν = ν)
    (hcosh : Integrable Real.cosh ν) :
    let μ := Measure.map aShift (ν.withDensity fun z => ENNReal.ofReal (wInt z))
    let u := ∫ z, Real.cosh z ∂ν
    μ Set.univ = ENNReal.ofReal (u+hPot ν/2) ∧
    (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ) = ENNReal.ofReal (2*u) ∧
    (∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂μ) = ENNReal.ofReal u := by sorry
