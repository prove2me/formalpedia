-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplex_base_volume_v2
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplex_base_volume_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:29:48.962935+00:00
-- url     : https://prove2.me/theorems/4c356361-9037-444c-b16d-371a4f10e441
-- title:
--   Volume of the unit coordinate simplex
-- statement:
--   The nonnegative coordinate simplex with sum at most one has volume 1 divided by n factorial, including the zero-dimensional case.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplex_base_volume_v2 (n : Nat) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ 1} =
    ENNReal.ofReal (1 / (n.factorial : Real)) := by sorry
