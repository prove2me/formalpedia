-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegativeLawComplexLaplaceAnalyticV1
-- name    : Kyprianou.Ch02.nonnegativeLawComplexLaplaceAnalyticV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:37:22.801138+00:00
-- url     : https://prove2.me/theorems/cd49c048-9acf-43fb-ba67-98f7e8b7e372
-- title:
--   nonnegativeLawComplexLaplaceAnalytic
-- statement:
--   nonnegativeLawComplexLaplaceAnalytic
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.nonnegativeLawComplexLaplaceAnalyticV1
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q (Set.Iio (0 : ℝ)) = 0) :
    DiffContOnCl ℂ (fun z : ℂ => ∫ x, Complex.exp (-z * (x : ℂ)) ∂Q)
      {z : ℂ | 0 < z.re} ∧
    ∀ z : ℂ, 0 ≤ z.re → ‖∫ x, Complex.exp (-z * (x : ℂ)) ∂Q‖ ≤ 1 := by sorry
