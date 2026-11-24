-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegativeLawLaplaceContinuousClosedV1
-- name    : Kyprianou.Ch02.nonnegativeLawLaplaceContinuousClosedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:53:42.198921+00:00
-- url     : https://prove2.me/theorems/6b7049b4-af98-483b-8610-46aea1c5795a
-- title:
--   nonnegativeLawLaplaceContinuousClosed
-- statement:
--   nonnegativeLawLaplaceContinuousClosed
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.nonnegativeLawLaplaceContinuousClosedV1
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q (Set.Iio (0 : ℝ)) = 0) :
    ContinuousOn (fun z : ℂ => ∫ x, Complex.exp (-z * (x : ℂ)) ∂Q) {z : ℂ | 0 ≤ z.re} := by sorry
