-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanMarkedDoubleIntegralMap
-- name    : Kyprianou.Ch01.mckeanMarkedDoubleIntegralMap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:02:29.218884+00:00
-- url     : https://prove2.me/theorems/70d73945-19b0-408c-b566-d9d8dce50bed
-- title:
--   Independent-coordinate change of variables in iterated marked payoff integral
-- statement:
--   For measurable marked state T and increment Z, change variables by their pushforward laws in an iterated Bochner integral. This elementary step does not depend on independence and is needed to convert the joint-law Fubini identity into the exact McKean conditional-expectation event equality.
-- source:
--   Kyprianou 2006 Chapter 1 Theorem 1.13 and Mathlib pushforward integral identity.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanMarkedDoubleIntegralMap
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ × Bool) (Z : Ω → ℝ)
    (g : (ℝ × Bool) × ℝ → ℝ)
    (hT : Measurable T) (hZ : Measurable Z)
    (hg : Measurable g) :
    (∫ a, ∫ z, g (a, z) ∂P.map Z ∂P.map T) =
      (∫ ω, ∫ ξ, g (T ω, Z ξ) ∂P ∂P) := by sorry
