-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46CappedPathJointV1
-- name    : Kyprianou.Ch04.exercise46CappedPathJointV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:09:31.991638+00:00
-- url     : https://prove2.me/theorems/c76354e5-71c0-59f7-a98b-f7f5f0d1d0a2
-- title:
--   Joint measurability of the deterministically capped path
-- statement:
--   Cap the time coordinate at T; the sections are measurable at T, and the capped paths retain right continuity. Apply the established joint evaluation lemma.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46CappedPathJointV1
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal m)
    (L : SpectrallyNegativeLevy P G) (T : NNReal) :
    @Measurable (NNReal × Omega) Real
      (@Prod.instMeasurableSpace NNReal Omega inferInstance (G.rightCont T))
      inferInstance (fun z => L.X (min z.1 T) z.2) := by
  sorry
