-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_integral_eq_of_zero_outside_Icc
-- name    : OAI.PiExponent.DeterminantContradiction.integral_eq_of_zero_outside_Icc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:26:19.687284+00:00
-- url     : https://prove2.me/theorems/d485750a-9369-48f1-b396-2a7245a4435d
-- title:
--   Restrict an integral to an interval containing the support
-- statement:
--   An integrable real function that vanishes outside [0,A] has the same whole-line integral as its integral over [0,A].

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.integral_eq_of_zero_outside_Icc {A : Real} (g : Real → Real) (hg : MeasureTheory.Integrable g MeasureTheory.volume) (hzero : ∀ t, t ∉ Set.Icc (0 : Real) A → g t = 0) : (∫ t, g t ∂MeasureTheory.volume) = (∫ t in Set.Icc (0 : Real) A, g t ∂MeasureTheory.volume) := by sorry
