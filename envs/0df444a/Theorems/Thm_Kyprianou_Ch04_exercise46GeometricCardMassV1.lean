-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46GeometricCardMassV1
-- name    : Kyprianou.Ch04.exercise46GeometricCardMassV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T12:30:32.758441+00:00
-- url     : https://prove2.me/theorems/a9fc13eb-2f44-5bd0-baf3-11fb1c8a93bb
-- title:
--   The difference of consecutive geometric tail probabilities yields the cardinality probability mass.
-- statement:
--   The difference of consecutive geometric tail probabilities yields the cardinality probability mass.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.6(ii).

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46GeometricCardMassV1
    {Omega T : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (B : Omega → Set T) (p : Real) (hp : 0 < p) (hp1 : p < 1)
    (htail : ∀ k : Nat,
      (P {omega | ((k + 1 : Nat) : ENat) ≤ (B omega).encard}).toReal =
        (1 - p) ^ k)
    (hmeas : ∀ k : Nat, MeasurableSet
      {omega | ((k + 1 : Nat) : ENat) ≤ (B omega).encard})
    (hfinite : ∀ᵐ omega ∂P, (B omega).Finite) :
    ∀ k : Nat, (P {omega | (B omega).ncard = k + 1}).toReal =
      p * (1 - p) ^ k := by
  sorry
