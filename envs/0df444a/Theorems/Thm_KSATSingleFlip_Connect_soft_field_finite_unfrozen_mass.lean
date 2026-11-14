-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_finite_unfrozen_mass
-- name    : KSATSingleFlip.Connect.soft_field_finite_unfrozen_mass
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:53:59.265485+00:00
-- url     : https://prove2.me/theorems/448400ac-0688-454a-8706-0054dc2a69d0
-- title:
--   Finite unfrozen mass implies finite measure and cosh integrability
-- statement:
--   If ∫cosh(z)ν(dz) is finite for a measure on the real line, then ν is a finite measure and cosh is Bochner-integrable with respect to ν. This turns the paper’s finite-unfrozen-mass hypothesis into the finiteness assumptions used in the update proofs.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

theorem KSATSingleFlip.Connect.soft_field_finite_unfrozen_mass (ν : Measure ℝ)
    (hu : (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν) ≠ ∞) :
    Integrable Real.cosh ν ∧ IsFiniteMeasure ν := by sorry
