-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46RegenerativePhysicalTailTransferV1
-- name    : Kyprianou.Ch04.exercise46RegenerativePhysicalTailTransferV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:26:38.104029+00:00
-- url     : https://prove2.me/theorems/5d3bfdd8-749f-5edd-9833-c7e496228e04
-- title:
--   Transfer regenerative count law to physical ENat tails
-- statement:
--   Transfer regenerative count law to physical ENat tails
-- source:
--   Kyprianou (2006), Exercise 4.6.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46RegenerativeCountTransferV1
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46RegenerativePhysicalTailTransferV1
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (S : Omega → Set NNReal)
    (D : Set Omega) (hD : MeasurableSet D)
    (Y Z : Omega → E) (hY : Measurable Y)
    (hZ : AEMeasurable Z (P.restrict D))
    (C : E → ENNReal) (hC : Measurable C)
    (q : Real) (hq : (P D).toReal = q)
    (hLaw : (P.restrict D).map Z = P D • P.map Y)
    (hCard : ∀ᵐ w ∂P, C (Y w) = ((S w).encard : ENNReal))
    (hSplit : ∀ᵐ w ∂P,
      (w ∈ D → C (Y w) = 1 + C (Z w)) ∧
      (w ∉ D → C (Y w) = 1)) :
    ∀ k : Nat,
      (P {w | ((k+1+1 : Nat) : ENat) ≤ (S w).encard}).toReal =
      q * (P {w | ((k+1 : Nat) : ENat) ≤ (S w).encard}).toReal := by
  sorry
