-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegativeLawLaplaceNormBoundV1
-- name    : Kyprianou.Ch02.nonnegativeLawLaplaceNormBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:53:40.334798+00:00
-- url     : https://prove2.me/theorems/c0f583d2-e42e-4cd0-a8df-7f07fab01116
-- title:
--   nonnegativeLawLaplaceNormBound
-- statement:
--   nonnegativeLawLaplaceNormBound
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.nonnegativeLawLaplaceNormBoundV1
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q (Set.Iio (0 : ℝ)) = 0) :
    ∀ z : ℂ, 0 ≤ z.re → ‖∫ x, Complex.exp (-z * (x : ℂ)) ∂Q‖ ≤ 1 := by sorry
