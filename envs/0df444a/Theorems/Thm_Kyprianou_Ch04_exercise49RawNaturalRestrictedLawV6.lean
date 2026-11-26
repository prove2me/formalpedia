-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49RawNaturalRestrictedLawV6
-- name    : Kyprianou.Ch04.exercise49RawNaturalRestrictedLawV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:33:23.848259+00:00
-- url     : https://prove2.me/theorems/625f3c2f-b1a3-4afe-8065-054c0609bfd4
-- title:
--   exercise49RawNaturalRestrictedLawV6
-- statement:
--   exercise49RawNaturalRestrictedLawV6
-- source:
--   Exercise 4.9(iii): corrected ladder renewal proof

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49RawNaturalRestrictedLawV6
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t))
    (s : NNReal) (B : Set Ω) (hB : MeasurableSet[Kyprianou.Ch01.naturalSigma X s] B) :
    Measure.map (fun w u => X (s + u) w - X s w) (P.restrict B) =
      P B • Measure.map (fun w u => X u w) P := by
  sorry
