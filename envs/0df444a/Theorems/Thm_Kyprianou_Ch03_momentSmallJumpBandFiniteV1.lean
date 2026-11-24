-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentSmallJumpBandFiniteV1
-- name    : Kyprianou.Ch03.momentSmallJumpBandFiniteV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T13:20:23.111572+00:00
-- url     : https://prove2.me/theorems/efb5af11-acf8-4ae6-9ffc-8a86a17af34d
-- title:
--   Finite Lévy measure of a small-jump annulus
-- statement:
--   On the annulus min(1,x²)≥min(1,e²)>0; apply the integral Markov bound.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; finite compensated small-jump approximation, reusing Chapter 8 finite transform construction and published compound-Poisson transform.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentSmallJumpBandFiniteV1
    (T : ProbabilityTheory.LevyKhintchineTriple) (e : Real) (he : 0 < e) :
    IsFiniteMeasure (T.levyMeasure.restrict {x : Real | e ≤ |x| ∧ |x| < 1}) := by sorry
