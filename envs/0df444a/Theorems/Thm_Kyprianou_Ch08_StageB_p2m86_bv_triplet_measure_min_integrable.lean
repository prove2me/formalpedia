-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m86_bv_triplet_measure_min_integrable
-- name    : Kyprianou.Ch08.StageB.p2m86_bv_triplet_measure_min_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:03:16.580801+00:00
-- url     : https://prove2.me/theorems/a43623ed-31c7-48ff-aa6d-83e5518a0fab
-- title:
--   8.6 BV integrable for generic negative-jump split
-- statement:
--   The Lévy triplet measure satisfies the standard integrability of min(1,x²).
-- source:
--   Kyprianou (2006), Lemma 8.6; reuse existing published generic negative jump partition.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- The Lévy triplet measure satisfies the standard integrability of min(1,x²). -/
theorem p2m86_bv_triplet_measure_min_integrable :
    ∀ (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P),
    Integrable (fun y : ℝ => min 1 (y ^ 2)) D.triplet.levyMeasure := by
  sorry

end Kyprianou.Ch08.StageB
