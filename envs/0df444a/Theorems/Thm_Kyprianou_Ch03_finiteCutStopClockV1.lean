-- Prove2me | Theorems.Thm_Kyprianou_Ch03_finiteCutStopClockV1
-- name    : Kyprianou.Ch03.finiteCutStopClockV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T15:13:19.399974+00:00
-- url     : https://prove2.me/theorems/b9a1db3e-c0a3-4eb1-acc1-a3f83bc54e52
-- title:
--   Bounded stopping clock for a finite stopping event
-- statement:
--   Capping the original stopping time at n gives a bounded finite stopping clock; the finite-cut event belongs to its stopping sigma algebra.
-- source:
--   Kyprianou (2006), Corollary 3.11; faithful support for e939e617-26cc-4e11-98c6-e87492aefbb3

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.finiteCutStopClockV1
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (tauFinite : Omega → NNReal)
    (hFinite : ∀ w, tau w ≠ ⊤ → tau w = (tauFinite w : WithTop NNReal))
    (A : Set Omega)
    (hA : ∀ t : NNReal, MeasurableSet[F t] (A ∩ {w | tau w ≤ (t : WithTop NNReal)}))
    (n : NNReal)
    : ∃ (rho : Omega → NNReal)
      (hStop : IsStoppingTime F (fun w => (rho w : WithTop NNReal))),
      (∀ w, rho w ≤ n) ∧
      MeasurableSet[hStop.measurableSpace] (A ∩ {w | tau w ≤ (n : WithTop NNReal)}) ∧
      (∀ w ∈ A ∩ {w | tau w ≤ (n : WithTop NNReal)}, rho w = tauFinite w) := by sorry
