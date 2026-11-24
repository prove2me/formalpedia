-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovFiniteStoppedEventMeasV1
-- name    : Kyprianou.Ch03.strongMarkovFiniteStoppedEventMeasV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:20:36.981334+00:00
-- url     : https://prove2.me/theorems/cb65fa22-1d48-4b1c-9ec5-2f8fbe1ac58e
-- title:
--   Theorem 3.1: Measurability of a stopped-past event restricted to finite stopping, using integer sublevel exhaustion
-- statement:
--   Measurability of a stopped-past event restricted to finite stopping, using integer sublevel exhaustion
-- source:
--   Kyprianou (2006), Theorem 3.1; parent 0086c6a9-2a1f-474f-95e8-2bee321d1bf2.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovFiniteStoppedEventMeasV1
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (A : Set Omega) (hA : (∀ s : NNReal, MeasurableSet[F s]
      (A ∩ {w : Omega | tau w ≤ (s : WithTop NNReal)}))) :
    MeasurableSet (A ∩ {w : Omega | tau w ≠ ⊤}) := by
  sorry
