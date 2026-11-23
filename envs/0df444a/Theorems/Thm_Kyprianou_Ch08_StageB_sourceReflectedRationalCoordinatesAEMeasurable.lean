-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_sourceReflectedRationalCoordinatesAEMeasurable
-- name    : Kyprianou.Ch08.StageB.sourceReflectedRationalCoordinatesAEMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:29:28.170209+00:00
-- url     : https://prove2.me/theorems/bbb3a632-36a6-45e2-8332-7c6135ae05ff
-- title:
--   Lemma 8.2: reflected original surplus has a.e. measurable coordinates at every nonnegative rational time
-- statement:
--   For each nonnegative rational time, the actual reflected spectrally negative surplus at that time is measurable modulo the original probability law. Derive from the original model's coordinate a.e. measurability and cadlag path separability, representing its running supremum by a countable right-dense set of rational time evaluations plus the endpoint. Preserve the original reflection definition and measure.
-- source:
--   Source model D.levy.stationary_increments and D.levy.cadlag_ae, plus exact runningSup and reflectAtSup definitions in StageCFoundation. Source-specific child of f9a67c26 in connected Lemma 8.2 branch.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.sourceReflectedRationalCoordinatesAEMeasurable
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) :
    ∀ r : ℚ, 0 ≤ r →
      AEMeasurable
        (fun ω => reflectAtSup D.X 0 (r : ℝ).toNNReal ω) P := by
  sorry
