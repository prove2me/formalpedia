-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegativeLawLaplaceDifferentiableV1
-- name    : Kyprianou.Ch02.nonnegativeLawLaplaceDifferentiableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:53:48.123569+00:00
-- url     : https://prove2.me/theorems/a5038681-dc83-4471-9b16-4a5cf5c2583c
-- title:
--   nonnegativeLawLaplaceDifferentiable
-- statement:
--   nonnegativeLawLaplaceDifferentiable
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.nonnegativeLawLaplaceDifferentiableV1
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q (Set.Iio (0 : ℝ)) = 0) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ x, Complex.exp (-z * (x : ℂ)) ∂Q) {z : ℂ | 0 < z.re} := by sorry
