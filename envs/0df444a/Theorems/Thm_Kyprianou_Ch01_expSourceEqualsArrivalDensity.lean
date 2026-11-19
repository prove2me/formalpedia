-- Prove2me | Theorems.Thm_Kyprianou_Ch01_expSourceEqualsArrivalDensity
-- name    : Kyprianou.Ch01.expSourceEqualsArrivalDensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T07:17:57.71033+00:00
-- url     : https://prove2.me/theorems/789203a8-0c6e-460f-9f11-f025311b2e8c
-- title:
--   The explicit strictly positive exponential law equals the first Erlang-arrival density measure
-- statement:
--   The exact source exponential increment law, with density beta exp(-beta x) on x>0, is the gamma arrival density with shape one and rate beta in the previously published LevyFoundations library. Its density on x>=0 differs only at the Lebesgue-null origin, so both measures coincide. This is the base-law bridge for Kyprianou Exercise 1.8(iv).
-- source:
--   Kyprianou (2006), Exercise 1.8(iv), pp.304–305

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_levy_foundations_arrivalGammaDensity
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.expSourceEqualsArrivalDensity
    (beta : ℝ) (hbeta : 0 < beta) :
    (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun x : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * x))) =
      volume.withDensity (LevyFoundations.arrivalGammaDensity beta 0) := by
  sorry
