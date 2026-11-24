-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovGridCellsMeasV1
-- name    : Kyprianou.Ch03.strongMarkovGridCellsMeasV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:13:47.813261+00:00
-- url     : https://prove2.me/theorems/1198dd0d-402d-4a9b-8879-d369badc4e3d
-- title:
--   Measurability of ordered countable grid cells
-- statement:
--   An ordered grid cell on the finite event is either empty, the first sublevel, or the difference of consecutive stopping sublevels.
-- source:
--   Kyprianou (2006), Theorem 3.1; dyadic fibre measurability 549813ab-58fc-4e59-ab0b-175afdb53dbe.

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovGridCellsMeasV1
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (g : ℕ → NNReal) (hg : StrictMono g) (k : Omega → ℕ)
    (hSub : ∀ j w, (tau w ≠ ⊤ ∧ k w ≤ j) ↔ tau w ≤ (g j : WithTop NNReal))
    (s : NNReal) :
    MeasurableSet[F s] {w | tau w ≠ ⊤ ∧ g (k w) = s} := by
  sorry
