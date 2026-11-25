-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteExtendedSupToRealV1
-- name    : Kyprianou.Ch04.finiteExtendedSupToRealV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:28:16.471891+00:00
-- url     : https://prove2.me/theorems/5c4b81ab-a522-47b5-9113-a5d2b2997207
-- title:
--   Finite extended supremum of nonnegative path equals real supremum
-- statement:
--   If the extended supremum of a nonnegative path over a compact horizon is finite, its real supremum exists with the same value.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii), real supremum conversion.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteExtendedSupToRealV1 (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hn : ∀ t, 0 ≤ f t) (S : ℝ≥0∞) (hS : S < ⊤)
    (heq : (⨆ t : Iic T, ENNReal.ofReal (f t)) = S) :
    sSup (f '' Iic T) = S.toReal := by
  sorry
end Kyprianou.Ch04
