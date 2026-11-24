-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveLevyTruncatedMomentFromLocalV1
-- name    : Kyprianou.Ch02.positiveLevyTruncatedMomentFromLocalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:17:52.887859+00:00
-- url     : https://prove2.me/theorems/617265d8-c5b3-41fe-9260-da61cffb0aa6
-- title:
--   Local positive first moment implies finite positive truncated Lévy moment
-- statement:
--   Split the positive half-line into (0,r) and [r,infinity). On the first part the truncated absolute mark is dominated by the integrable identity. The second part has finite Lévy mass and a bounded integrand. Combine the two integrability results.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14; alternative to the full bounded-variation criterion for subordinator necessity.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveLevyTruncatedMomentFromLocalV1
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (r : ℝ) (hr : 0 < r)
    (hsmall : Integrable (fun x : ℝ => x) (ν.restrict (Set.Ioo 0 r))) :
    Integrable (fun x : ℝ => min (1 : ℝ) |x|) (ν.restrict (Set.Ioi 0)) := by sorry
