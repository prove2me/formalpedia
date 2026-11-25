-- Prove2me | Theorems.Thm_Kyprianou_Ch04_idleFiniteRegulatorToStrictCrossingV1
-- name    : Kyprianou.Ch04.idleFiniteRegulatorToStrictCrossingV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:24:12.041786+00:00
-- url     : https://prove2.me/theorems/4ee8a4ad-8280-4049-aeef-4bd3090b3787
-- title:
--   Finite regulator identity implies the strict tail crossing equivalence
-- statement:
--   Use the strict supremum test for ENNReal, positive finite drift scaling, and strict crossing of the real supremum over finite horizons. Conversely any crossing time is contained in a sufficiently large natural horizon.
-- source:
--   Kyprianou (2006), Theorem 4.1, strict idle-time tail.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.idleFiniteRegulatorToStrictCrossingV1
    (f : NNReal → Real) (d w : Real) (hd : 0 < d)
    (hbdd : ∀ t : NNReal, BddAbove (f '' Iic t))
    (J : Nat → ENNReal)
    (hJ : ∀ n : Nat,
      ENNReal.ofReal (max w (sSup (f '' Iic (n : NNReal))) - w) =
        ENNReal.ofReal d * J n) :
    ∀ x : Real, 0 ≤ x →
      (ENNReal.ofReal x < (⨆ n : Nat, J n) ↔
        ∃ t : NNReal, w + d * x < f t) := by
  sorry
