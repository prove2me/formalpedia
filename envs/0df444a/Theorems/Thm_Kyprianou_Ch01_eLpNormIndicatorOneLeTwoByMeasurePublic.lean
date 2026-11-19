-- Prove2me | Theorems.Thm_Kyprianou_Ch01_eLpNormIndicatorOneLeTwoByMeasurePublic
-- name    : Kyprianou.Ch01.eLpNormIndicatorOneLeTwoByMeasurePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:15:00.037593+00:00
-- url     : https://prove2.me/theorems/cd7e3e94-c8f6-4f8a-9681-cf694a36ba33
-- title:
--   Event-restricted L1 norm bounded by the L2 norm times square root event measure
-- statement:
--   For any almost-everywhere strongly measurable real-valued function on an arbitrary measure space and measurable event s, the L1 norm of the function restricted to s is no greater than its full L2 norm multiplied by the square root of the measure of s. This is the Hölder/Lp exponent comparison on a restricted measure; it establishes uniform absolute continuity from bounded L2 norms.
-- source:
--   Pinned Mathlib eLpNorm_le_eLpNorm_mul_rpow_measure_univ; used in Kyprianou (2006) Chapter 1 stopped Brownian uniform-integrability proof.

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic.NormNum
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.eLpNormIndicatorOneLeTwoByMeasurePublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f P)
    (s : Set Ω) (hs : MeasurableSet s) :
    eLpNorm (s.indicator f) 1 P ≤
      eLpNorm f 2 P * (P s) ^ (1 / 2 : ℝ) := by sorry
