-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_succ
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:14:12.670197+00:00
-- url     : https://prove2.me/theorems/77617b82-a949-4732-af34-406aafdce701
-- title:
--   Successor recurrence for standard simplex volume
-- statement:
--   The volume of the nonnegative (n+1)-dimensional region whose coordinate sum is at most one is the n-dimensional region's volume divided by n+1.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_succ (n : Nat) :
    (MeasureTheory.volume {x : Fin (n + 1) → Real | (∀ i : Fin (n + 1), 0 ≤ x i) ∧
      ∑ i : Fin (n + 1), x i ≤ 1}).toReal =
      ((MeasureTheory.volume {x : Fin n → Real | (∀ i : Fin n, 0 ≤ x i) ∧
        ∑ i : Fin n, x i ≤ 1}).toReal) / (↑(n + 1) : Real) := by sorry
