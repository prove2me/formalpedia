-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_finite_intensity
-- name    : KSATSingleFlip.Connect.soft_field_finite_intensity
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:25:39.43669+00:00
-- url     : https://prove2.me/theorems/0eb38c47-6216-48b3-81dd-04bee69677c1
-- title:
--   Finite unfrozen mass gives finite Poisson intensity
-- statement:
--   If the scaled unfrozen mass ∫ cosh(z) ν(dz) is finite, then the w-weighted Poisson intensity defining the soft-field update is finite. This bridges the finiteness assumption before Lemma 4.5 to the compound Poisson normalization.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_field_finite_intensity (ν : Measure ℝ)
    (hu : (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν) ≠ ∞) :
    (ν.withDensity fun z => ENNReal.ofReal (wInt z)) Set.univ ≠ ∞ := by sorry
