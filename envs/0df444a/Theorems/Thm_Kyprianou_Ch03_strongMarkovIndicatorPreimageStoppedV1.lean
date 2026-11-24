-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovIndicatorPreimageStoppedV1
-- name    : Kyprianou.Ch03.strongMarkovIndicatorPreimageStoppedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:20:44.106486+00:00
-- url     : https://prove2.me/theorems/d8994d72-2572-457c-8a9b-fc1e6c4618a5
-- title:
--   Theorem 3.1: A Borel preimage of a stopped-event indicator is a stopped event
-- statement:
--   A Borel preimage of a stopped-event indicator is a stopped event
-- source:
--   Kyprianou (2006), Theorem 3.1; parent 0086c6a9-2a1f-474f-95e8-2bee321d1bf2.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovIndicatorPreimageStoppedV1
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (A : Set Omega) (hA : (∀ s : NNReal, MeasurableSet[F s]
      (A ∩ {w : Omega | tau w ≤ (s : WithTop NNReal)})))
    (S : Set Real) (hS : MeasurableSet S) :
    ∀ s : NNReal, MeasurableSet[F s]
      ((Set.indicator A (fun _ : Omega => (1 : Real)) ⁻¹' S) ∩
        {w : Omega | tau w ≤ (s : WithTop NNReal)}) := by
  sorry
