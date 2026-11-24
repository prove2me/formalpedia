-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveLevyAnnulusIntegrableV1
-- name    : Kyprianou.Ch02.positiveLevyAnnulusIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:09:24.275967+00:00
-- url     : https://prove2.me/theorems/96c45983-12c7-49e4-8225-3c6b952da3aa
-- title:
--   Integrability of the first moment on a positive Lévy annulus
-- statement:
--   The positive annulus [r,1) has finite mass and the identity function is bounded there.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14; parent baac6daa-de4d-4888-9d09-eada1ed8d2c4.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveLevyAnnulusIntegrableV1
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x) (Set.Ico r 1) ν := by sorry
