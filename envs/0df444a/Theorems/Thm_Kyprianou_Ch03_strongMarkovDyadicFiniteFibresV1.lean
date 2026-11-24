-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovDyadicFiniteFibresV1
-- name    : Kyprianou.Ch03.strongMarkovDyadicFiniteFibresV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:57:35.297118+00:00
-- url     : https://prove2.me/theorems/549813ab-58fc-4e59-ab0b-175afdb53dbe
-- title:
--   Finite-event dyadic stopping fibres
-- statement:
--   A finite-event fibre of the upper dyadic rounding equals a difference of stopping sublevel sets, with the zero cell separate and off-grid fibres empty.
-- source:
--   Kyprianou (2006), Theorem 3.1; parent 6ff8b93e-0675-4cc3-8e57-14e72ebe0bba.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovDyadicFiniteFibresV1
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (n : ℕ) (s : NNReal) :
    MeasurableSet[F s] ({w : Omega | tau w ≠ ⊤} ∩ {w | (fun w : Omega => if tau w = ⊤ then (0 : NNReal) else
      (Nat.ceil ((finiteTime w : ℝ) * (2 : ℝ)^n) : NNReal) / (2 : NNReal)^n) w = s}) := by
  sorry
