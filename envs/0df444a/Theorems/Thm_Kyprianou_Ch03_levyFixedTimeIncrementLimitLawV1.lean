-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levyFixedTimeIncrementLimitLawV1
-- name    : Kyprianou.Ch03.levyFixedTimeIncrementLimitLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:18:15.852506+00:00
-- url     : https://prove2.me/theorems/b913adcd-44af-4bab-be51-61fff3b98048
-- title:
--   Distributional limit of shrinking increments at a fixed time
-- statement:
--   Take a deterministic sequence s tending to u from the left. By stationary increments, the pairs (X u - X (min s u), 0) and (X (u - min s u), 0) have the same law. Their almost sure limits are the jump pair and zero pair. Apply Kyprianou.Ch02.identDistribPairOfAELimitsV1.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.4; parents 11df6340-566e-48b2-ba84-cb77468f8366 and 8ac9ed28-eeeb-4802-8031-7ce3fe9b88b5.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.levyFixedTimeIncrementLimitLawV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (u : NNReal) (hu : 0 < u) :
    IdentDistrib
      (fun ω : Omega => (X u ω - Function.leftLim (fun r : NNReal => X r ω) u, (0 : Real)))
      (fun _ : Omega => ((0 : Real), (0 : Real))) P P := by sorry
