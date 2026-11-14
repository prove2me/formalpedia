-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_iterates_well_defined
-- name    : KSATSingleFlip.Connect.soft_field_iterates_well_defined
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:56:58.742193+00:00
-- url     : https://prove2.me/theorems/30ce5f45-ce0f-4028-adcb-c9c8fb452dc7
-- title:
--   Soft-field iterates have finite mass and exact mass recursions
-- statement:
--   For every real γ and every finite iteration r, the soft-field iterate started from the zero measure is symmetric, finite and has finite unfrozen mass. Its next iterate satisfies the exact mass and unfrozen-mass recursions from Definition 4.2. This gives well-defined iterates but does not assert the critical-threshold theorem.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and equation (4.8), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_field_iterates_well_defined (γ : ℝ) : ∀ r : ℕ,
    IsFiniteMeasure (nuIter γ r) ∧
    Measure.map (fun z : ℝ => -z) (nuIter γ r) = nuIter γ r ∧
    (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂(nuIter γ r)) ≠ ∞ ∧
    (massM (nuIter γ (r+1))).toReal = Real.exp (-γ)*Real.exp (hPot (nuIter γ r)) ∧
    (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂(nuIter γ (r+1))) =
      ENNReal.ofReal (Real.exp (-γ)*Real.exp ((∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂(nuIter γ r)).toReal)) := by sorry
