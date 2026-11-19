-- Prove2me | Theorems.Thm_Kyprianou_Ch01_realHarmonicIntegralFormulaV2
-- name    : Kyprianou.Ch01.realHarmonicIntegralFormulaV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:47:55.005878+00:00
-- url     : https://prove2.me/theorems/b47d1df2-1ed3-4b38-8cde-74630f98e8ce
-- title:
--   Real harmonic logarithmic integral over nonnegative finite intervals (Lebesgue syntax)
-- statement:
--   The elementary primitive of 1/(1+r) on the nonnegative real line is logarithm(1+r); the finite interval integral from zero to any nonnegative s equals log(1+s). The exact identity is a reusable analytic supporting lemma for divergence of the extended harmonic reciprocal-occupation integral.
-- source:
--   Elementary real calculus, pinned Mathlib intervalIntegral.integral_comp_add_left and integral_one_div; Kyprianou (2006), Chapter 1.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.NNReal.Basic
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01 Set Real
open scoped NNReal ENNReal Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.realHarmonicIntegralFormulaV2
    (s : ℝ≥0) :
    (∫ r in Set.Ioc (0 : ℝ) (s : ℝ),
      ((1 : ℝ) / (1 + r)) ∂volume) =
        Real.log (1 + (s : ℝ)) := by
  sorry
