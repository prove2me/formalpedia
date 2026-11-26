-- Prove2me | Theorems.Thm_Kyprianou_Ch04_openHitStoppingTimeOfAE
-- name    : Kyprianou.Ch04.openHitStoppingTimeOfAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:11:14.923604+00:00
-- url     : https://prove2.me/theorems/003d32b3-65c6-525b-be5e-c6005126a232
-- title:
--   openHitStoppingTimeOfAE
-- statement:
--   The first hit of an open set by an adapted a.s. right-continuous process is a stopping time for a right-continuous filtration containing all subsets of ambient null sets.
-- source:
--   Kyprianou (2006), Exercise 4.3(i)-(ii), pp. 106-107.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Open-set hitting of an adapted a.s. right-continuous process is a stopping time
in a right-continuous filtration containing all subsets of ambient null sets. -/
theorem Kyprianou.Ch04.openHitStoppingTimeOfAE {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Omega), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (Y : NNReal → Omega → ℝ) (hY : Adapted F Y)
    (hPath : ∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => Y u w) (Set.Ici t) t)
    (B : Set ℝ) (hB : IsOpen B) :
    IsStoppingTime F (fun w => sInf {u : WithTop NNReal |
      ∃ r : NNReal, u = ↑r ∧ Y r w ∈ B}) := by
  sorry
