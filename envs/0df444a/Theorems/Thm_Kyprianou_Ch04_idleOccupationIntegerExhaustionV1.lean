-- Prove2me | Theorems.Thm_Kyprianou_Ch04_idleOccupationIntegerExhaustionV1
-- name    : Kyprianou.Ch04.idleOccupationIntegerExhaustionV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:24:08.094607+00:00
-- url     : https://prove2.me/theorems/b9261309-f11e-44be-adb7-809eb5123082
-- title:
--   Nonnegative half-line integral equals supremum over closed integer horizons
-- statement:
--   Use the increasing closed intervals [0,n] with union [0,infinity), and apply monotone convergence to the interval indicators multiplied by g.
-- source:
--   Kyprianou (2006), Theorem 4.1, infinite-horizon regulator limit.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.idleOccupationIntegerExhaustionV1
    (g : Real → ENNReal) (hg : Measurable g) :
    (∫⁻ t in Ici (0 : Real), g t ∂volume) =
      ⨆ n : Nat, ∫⁻ t in Icc (0 : Real) (n : Real), g t ∂volume := by
  sorry
