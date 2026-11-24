-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovRestrictedProductOfPreimagesV1
-- name    : Kyprianou.Ch03.strongMarkovRestrictedProductOfPreimagesV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T07:20:41.428579+00:00
-- url     : https://prove2.me/theorems/7c2f6ec4-0853-4bf2-92df-f4f9606ad97b
-- title:
--   Theorem 3.1: General finite-restriction product law from restricted laws on preimages of a statistic
-- statement:
--   General finite-restriction product law from restricted laws on preimages of a statistic
-- source:
--   Kyprianou (2006), Theorem 3.1; parent 0086c6a9-2a1f-474f-95e8-2bee321d1bf2.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovRestrictedProductOfPreimagesV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (D : Set Omega) (hD : MeasurableSet D)
    (I : Omega → Real) (Y : Omega → (NNReal → Real))
    (nu : Measure (NNReal → Real))
    (hI : AEMeasurable I (P.restrict D))
    (hY : AEMeasurable Y (P.restrict D))
    (hLaw : ∀ S : Set Real, MeasurableSet S →
      MeasurableSet (I ⁻¹' S ∩ D) ∧
      Measure.map Y (P.restrict (I ⁻¹' S ∩ D)) =
        P (I ⁻¹' S ∩ D) • nu) :
    Measure.map (fun w => (I w, Y w)) (P.restrict D) =
      (Measure.map I (P.restrict D)).prod nu := by
  sorry
