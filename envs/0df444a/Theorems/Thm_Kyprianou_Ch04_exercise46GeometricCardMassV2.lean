-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46GeometricCardMassV2
-- name    : Kyprianou.Ch04.exercise46GeometricCardMassV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T14:53:34.952962+00:00
-- url     : https://prove2.me/theorems/1be988bc-027e-4b04-904d-1ffd392f6d71
-- title:
--   Geometric cardinal mass from almost-sure measurable tail representatives
-- statement:
--   Derive the geometric mass formula using measurable representatives of tail events rather than raw measurable sets.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46GeometricCardMassV2
    {Omega T : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (B : Omega → Set T) (p : Real) (hp : 0 < p) (hp1 : p < 1)
    (htail : ∀ k : Nat,
      (P {omega | ((k + 1 : Nat) : ENat) ≤ (B omega).encard}).toReal =
        (1 - p) ^ k)
    (hmeas : ∀ k : Nat, ∃ S : Set Omega, MeasurableSet S ∧
      S =ᵐ[P] {omega | ((k + 1 : Nat) : ENat) ≤ (B omega).encard})
    (hfinite : ∀ᵐ omega ∂P, (B omega).Finite) :
    ∀ k : Nat, (P {omega | (B omega).ncard = k + 1}).toReal =
      p * (1 - p) ^ k := by
  sorry
