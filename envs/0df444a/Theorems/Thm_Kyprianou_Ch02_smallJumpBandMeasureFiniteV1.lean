-- Prove2me | Theorems.Thm_Kyprianou_Ch02_smallJumpBandMeasureFiniteV1
-- name    : Kyprianou.Ch02.smallJumpBandMeasureFiniteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:28:31.475035+00:00
-- url     : https://prove2.me/theorems/417d53b0-6d0c-41ad-937b-807f6e5d8e93
-- title:
--   A compensated finite small-jump band has finite Lévy measure
-- statement:
--   A Lévy measure assigns finite mass to the marks whose absolute value is at least a positive cutoff and strictly less than one.
-- source:
--   Kyprianou (2006), Chapter 2, finite small-jump band. Extract the already accepted Markov-inequality argument in compensatedBandIsL2MartingaleCorrected, avoiding the import collision in the existing LeanLevy tail-finiteness theorem.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.smallJumpBandMeasureFiniteV1
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (e : ℝ) (he : 0 < e) :
    levyMeasure {x : ℝ | e ≤ |x| ∧ |x| < 1} < ⊤ := by sorry
