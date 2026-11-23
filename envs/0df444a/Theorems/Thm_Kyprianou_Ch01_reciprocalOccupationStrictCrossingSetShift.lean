-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationStrictCrossingSetShift
-- name    : Kyprianou.Ch01.reciprocalOccupationStrictCrossingSetShift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:02:51.35058+00:00
-- url     : https://prove2.me/theorems/5e07d1c1-d539-4e55-83f3-9bc5c011790a
-- title:
--   Strict inverse-occupation crossing times translate by the prefix length
-- statement:
--   For branching time t at least A/y, the set of physical times at which the reciprocal-occupation clock of X strictly exceeds t is exactly A plus the set of tail physical times at which its occupation exceeds t-A/y. The proof uses the deterministic occupation-integral shift, monotonicity, and cancellation by finite A/y in ENNReal. This set equality lets the infimum-translation theorem solve the shift of strict right inverses.
-- source:
--   Kyprianou (2006), Section 1.3.4; deterministic reverse Lamperti clock translation at the first marked arrival.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reciprocalOccupationStrictCrossingSetShift
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω) :
    {u : ℝ≥0 | (t : ℝ≥0∞) < reciprocalOccupation X u ω} =
      (fun v : ℝ≥0 => Real.toNNReal A + v) ''
        {v : ℝ≥0 |
          ((Real.toNNReal ((t : ℝ) - A / (y : ℝ)) : ℝ≥0) : ℝ≥0∞) <
            reciprocalOccupation Y v ω} := by
  sorry
