-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46RegenerativeCountTransferV1
-- name    : Kyprianou.Ch04.exercise46RegenerativeCountTransferV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:08:47.92263+00:00
-- url     : https://prove2.me/theorems/2dce1926-f2e5-5ad0-96e0-8591e4076a3d
-- title:
--   Transfer of regenerative count tails under a restricted path law
-- statement:
--   A finite recovery event carries the original shifted path law. The count adds one on recovery and equals one otherwise, giving the tail probability recurrence.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46RegenerativeCountTransferV1
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (D : Set Omega) (hD : MeasurableSet D)
    (Y Z : Omega → E) (hY : Measurable Y)
    (hZ : AEMeasurable Z (P.restrict D))
    (C : E → ENNReal) (hC : Measurable C)
    (hLaw : (P.restrict D).map Z = P D • P.map Y)
    (hSplit : ∀ᵐ w ∂P, (w ∈ D → C (Y w) = 1 + C (Z w)) ∧
      (w ∉ D → C (Y w) = 1)) :
    ∀ k : Nat,
      (P {w | ((k+1+1 : Nat) : ENNReal) ≤ C (Y w)}).toReal =
        (P D).toReal * (P {w | ((k+1 : Nat) : ENNReal) ≤ C (Y w)}).toReal := by
  sorry
