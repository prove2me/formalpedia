-- Prove2me | Theorems.Thm_Kyprianou_Ch01_expDensityIoiTail
-- name    : Kyprianou.Ch01.expDensityIoiTail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T00:47:28.34001+00:00
-- url     : https://prove2.me/theorems/4547eba8-6a05-45af-b220-d4d7a41bb726
-- title:
--   Rate-beta exponential density with positive support has exact upper tail
-- statement:
--   For any positive rate beta, the probability law defined by restricting Lebesgue measure to strictly positive reals and weighting by beta exp(-beta e) has probability of (a, infinity) equal to exp(-beta a) for every a>=0. This is the source-exact exponential survival identity underpinning Exercise 1.8(iii).
-- source:
--   Kyprianou (2006) worked solution to Exercise 1.8(iii), printed page 304

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.expDensityIoiTail (beta : ℝ) (hbeta : 0 < beta) (a : ℝ) (ha : 0 ≤ a) :
  (((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun e : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * e))))
    (Set.Ioi a)).toReal = Real.exp (-beta * a) := by sorry
