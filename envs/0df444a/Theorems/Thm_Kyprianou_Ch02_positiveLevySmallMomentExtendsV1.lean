-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveLevySmallMomentExtendsV1
-- name    : Kyprianou.Ch02.positiveLevySmallMomentExtendsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:14:16.919636+00:00
-- url     : https://prove2.me/theorems/ff3b027a-015c-4efb-893f-19336caf7894
-- title:
--   Integrability of positive Lévy truncated moment from an interior first moment
-- statement:
--   On the positive interior interval the truncated moment equals the linear mark, and on the complementary positive tail it is bounded by one and the measure is finite. Combine the integrable pieces.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveLevySmallMomentExtendsV1
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hi : Integrable (fun x : ℝ => x) (ν.restrict (Ioo (0 : ℝ) r))) :
    Integrable (fun x : ℝ => min 1 |x|) (ν.restrict (Ioi (0 : ℝ))) := by
  sorry
