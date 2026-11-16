-- Prove2me | Theorems.Thm_Kyprianou_Ch06_probabilityFromIncrementCylinderLaw
-- name    : Kyprianou.Ch06.probabilityFromIncrementCylinderLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:06:01.210536+00:00
-- url     : https://prove2.me/theorems/96e7e45a-5ee2-4678-a404-b81850abacd0
-- title:
--   Chapter 6 compatibility: independent-increment cylinders force probability normalisation
-- statement:
--   The full finite-block independent-increment cylinder identity, including the empty block n=0, forces the underlying measure to have total mass one. The assertion is an exact logical consequence of the Chapter 6 IsRealLevyProcess independence axiom.
-- source:
--   Kyprianou (2006), Chapter 6 real Lévy-process independent-increments axiom; zero-dimensional cylinder case, an elementary reusable derived lemma.

import Mathlib

set_option autoImplicit false
open MeasureTheory
open scoped NNReal

theorem Kyprianou.Ch06.probabilityFromIncrementCylinderLaw
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hindep : ∀ (n : Nat) (times : Fin (n + 1) → NNReal),
      StrictMono times →
      ∀ A : Fin n → Set Real, (∀ i, MeasurableSet (A i)) →
        P {ω | ∀ i : Fin n,
          X (times i.succ) ω - X (times i.castSucc) ω ∈ A i} =
        ∏ i : Fin n,
          P {ω |
            X (times i.succ) ω - X (times i.castSucc) ω ∈ A i}) :
    P (Set.univ : Set Ω) = 1 := by sorry
