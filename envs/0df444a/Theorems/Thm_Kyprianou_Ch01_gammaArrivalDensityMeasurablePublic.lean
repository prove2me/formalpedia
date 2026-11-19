-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaArrivalDensityMeasurablePublic
-- name    : Kyprianou.Ch01.gammaArrivalDensityMeasurablePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:11:56.159859+00:00
-- url     : https://prove2.me/theorems/58cc6216-ce89-4da2-88a1-b58b9ae91ccf
-- title:
--   Measurability of the source gamma-arrival density for Tonelli integration
-- statement:
--   The exact gamma-arrival density defined by LevyFoundations is a measurable ENNReal-valued function for every rate and shape. It is an indicator of the Borel nonnegative half-line multiplied by a continuous real power-exponential expression followed by ENNReal.ofReal, so its measurability follows without importing a private cross-mission theorem.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.8(iv), measurable nonnegative Erlang density

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Definitions.Def_levy_foundations_arrivalGammaDensity
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaArrivalDensityMeasurablePublic
    (beta : ℝ) (n : ℕ) :
    Measurable (LevyFoundations.arrivalGammaDensity beta n) := by
  sorry
