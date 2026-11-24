-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovDyadicIndexMeasV1
-- name    : Kyprianou.Ch03.strongMarkovDyadicIndexMeasV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:14:34.167803+00:00
-- url     : https://prove2.me/theorems/27659cd6-5fc8-4524-8b4a-84f0e6dfa134
-- title:
--   Finite-event dyadic index cells
-- statement:
--   The exact finite-event dyadic index cell is measurable at its dyadic grid time, by differences of stopping sublevels.
-- source:
--   Kyprianou (2006), Theorem 3.1; parent 549813ab-58fc-4e59-ab0b-175afdb53dbe.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovDyadicIndexMeasV1
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (n j : ℕ) :
    MeasurableSet[F ((j : NNReal) / (2 : NNReal)^n)]
      {w : Omega | tau w ≠ ⊤ ∧ Nat.ceil ((finiteTime w : ℝ) * (2 : ℝ)^n) = j} := by
  sorry
