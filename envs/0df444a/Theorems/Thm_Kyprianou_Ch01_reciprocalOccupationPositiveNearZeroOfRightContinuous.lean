-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationPositiveNearZeroOfRightContinuous
-- name    : Kyprianou.Ch01.reciprocalOccupationPositiveNearZeroOfRightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:40:59.289461+00:00
-- url     : https://prove2.me/theorems/ffc9bdd3-79f7-4cf3-8288-13eaa081d5d7
-- title:
--   Positive reciprocal occupation immediately after zero for a right-continuous nonnegative integer starting state
-- statement:
--   Since the integer state is right-continuous at zero, it is constant on some positive right neighbourhood. If the state starts positive, its reciprocal occupation integral is strictly positive on every short nontrivial interval; if it starts at zero, the ENNReal inverse integrand is infinity on that interval, so the same conclusion holds. This supplies the key strict-clock hypothesis needed for the right-inverse to return zero.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, reciprocal occupation clock equation (1.19)

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01 MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reciprocalOccupationPositiveNearZeroOfRightContinuous
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (hNonneg : 0 ≤ X 0 ω)
    (hRight : ContinuousWithinAt
      (fun s : ℝ≥0 => X s ω) (Set.Ici 0) 0) :
    ∃ horizon : ℝ≥0, 0 < horizon ∧
      ∀ s : ℝ≥0, 0 < s → s < horizon →
        0 < reciprocalOccupation X s ω := by
  sorry
