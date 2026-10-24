-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_lintegral_congr_on_Icc
-- name    : OAI.PiExponent.DeterminantContradiction.lintegral_congr_on_Icc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:20:02.062263+00:00
-- url     : https://prove2.me/theorems/d625264f-b4d3-470c-bdd1-effa1b5f112a
-- title:
--   Congruence of lower integrals on an interval
-- statement:
--   Two nonnegative extended-real functions equal at every point of the closed unit interval have equal lower integrals over that interval.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem OAI.PiExponent.DeterminantContradiction.lintegral_congr_on_Icc (f g : Real → ENNReal)
    (h : ∀ t ∈ Set.Icc (0 : Real) 1, f t = g t) :
    ∫⁻ t in Set.Icc (0 : Real) 1, f t ∂MeasureTheory.volume =
      ∫⁻ t in Set.Icc (0 : Real) 1, g t ∂MeasureTheory.volume := by sorry
