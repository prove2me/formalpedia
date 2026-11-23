-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseReciprocalOccupationBracketFromCrossing
-- name    : Kyprianou.Ch01.inverseReciprocalOccupationBracketFromCrossing
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T15:29:47.37426+00:00
-- url     : https://prove2.me/theorems/2b7f95cf-137b-49fe-a5aa-6f6246654d5c
-- title:
--   Inverse of a nondecreasing occupation clock lies between pre-crossing and crossing times
-- statement:
--   The inverse of an extended-nonnegative occupation clock is the infimum of source times where the clock exceeds t. If all source times u<a have occupation at most t, while the occupation at b exceeds t, the infimum lies between a and b and is finite. This is a direct order-theoretic lower and upper bound on sInf, independent of stochastic properties and clock continuity.
-- source:
--   Kyprianou (2006) §1.3.4 and Mathlib sInf lower/upper bound properties

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseReciprocalOccupationBracketFromCrossing
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (t a b : ℝ≥0)
    (hBefore : ∀ u : ℝ≥0, u < a →
      reciprocalOccupation X u ω ≤ (t : ℝ≥0∞))
    (hCross : (t : ℝ≥0∞) < reciprocalOccupation X b ω) :
    ∃ s : ℝ≥0, a ≤ s ∧ s ≤ b ∧
      inverseReciprocalOccupation X t ω = (s : WithTop ℝ≥0) := by
  sorry
