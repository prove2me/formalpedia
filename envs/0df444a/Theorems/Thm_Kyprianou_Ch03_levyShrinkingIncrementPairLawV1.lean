-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levyShrinkingIncrementPairLawV1
-- name    : Kyprianou.Ch03.levyShrinkingIncrementPairLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:18:21.35846+00:00
-- url     : https://prove2.me/theorems/3fa27e0e-8ecf-4c0b-a041-8924044dbe77
-- title:
--   Stationary law for shrinking increment pairs
-- statement:
--   Use stationarity at min s u and lag u-min s u; the zero starting value identifies the lag increment with X at the lag. Postcompose both laws by the measurable map x ↦ (x,0).
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.4; parents 11df6340-566e-48b2-ba84-cb77468f8366 and 8ac9ed28-eeeb-4802-8031-7ce3fe9b88b5.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.levyShrinkingIncrementPairLawV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (u s : NNReal) :
    IdentDistrib
      (fun ω : Omega => (X u ω - X (min s u) ω, (0 : Real)))
      (fun ω : Omega => (X (u - min s u) ω, (0 : Real))) P P := by sorry
