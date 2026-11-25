-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46GeometricCardFiniteV1
-- name    : Kyprianou.Ch04.exercise46GeometricCardFiniteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T12:30:37.91919+00:00
-- url     : https://prove2.me/theorems/c8b63f55-7952-445c-bb17-a8bda4a7863b
-- title:
--   Vanishing geometric tail probabilities force almost-sure finiteness of a random set.
-- statement:
--   Vanishing geometric tail probabilities force almost-sure finiteness of a random set.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.6(ii).

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46GeometricCardFiniteV1
    {Omega T : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (B : Omega → Set T) (p : Real) (hp : 0 < p) (hp1 : p < 1)
    (htail : ∀ k : Nat,
      (P {omega | ((k + 1 : Nat) : ENat) ≤ (B omega).encard}).toReal =
        (1 - p) ^ k) :
    ∀ᵐ omega ∂P, (B omega).Finite := by
  sorry
