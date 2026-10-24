-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_interval_support
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_region_interval_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:28:25.478143+00:00
-- url     : https://prove2.me/theorems/5a572176-85c9-46da-88c1-fda7c5fab00e
-- title:
--   Restrict the simplex fiber integral to its support
-- statement:
--   The full-real integral of the constrained fiber volumes equals the interval integral from zero to `H` of the unconstrained slice volumes: outside that interval the constrained fiber is empty.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_region_interval_support (m : Nat) (H : Real) (hH : 0 < H) :
    (∫ t : Real,
        (MeasureTheory.volume {x : Fin m → Real | 0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal) =
      ∫ t in (0 : Real)..H,
        (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal := by sorry
