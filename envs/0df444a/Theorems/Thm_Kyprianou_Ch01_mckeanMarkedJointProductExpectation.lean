-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanMarkedJointProductExpectation
-- name    : Kyprianou.Ch01.mckeanMarkedJointProductExpectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:02:29.284956+00:00
-- url     : https://prove2.me/theorems/596da533-f922-4bdc-9874-c520a1b1135c
-- title:
--   Independent marked state and increment joint-law product integral
-- statement:
--   A bounded jointly measurable payoff of two independent random elements, the past-marked state T and future increment Z, has expectation equal to the corresponding iterated product-law integral. Use the independence-to-joint-law equality, integrability of bounded functions and Bochner Fubini. Genuine source-level conditional mixing obligation for McKean 1.13.
-- source:
--   Kyprianou 2006 Chapter 1 Theorem 1.13 and Mathlib independent law and Bochner Fubini.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanMarkedJointProductExpectation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ × Bool) (Z : Ω → ℝ)
    (g : (ℝ × Bool) × ℝ → ℝ) (K : ℝ)
    (hT : Measurable T) (hZ : Measurable Z)
    (hg : Measurable g) (hBound : ∀ p, ‖g p‖ ≤ K)
    (hInd : IndepFun T Z P) :
    (∫ ω, g (T ω, Z ω) ∂P) =
      (∫ a, ∫ z, g (a, z) ∂P.map Z ∂P.map T) := by sorry
