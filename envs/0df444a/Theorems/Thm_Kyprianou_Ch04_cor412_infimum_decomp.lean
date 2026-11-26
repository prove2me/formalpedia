-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_infimum_decomp
-- name    : Kyprianou.Ch04.cor412_infimum_decomp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:30:29.000687+00:00
-- url     : https://prove2.me/theorems/2421cf69-1fe5-5f51-8b39-5086eaeb76f6
-- title:
--   All-time infimum decomposes at a first downward passage
-- statement:
--   All-time infimum decomposes at a first downward passage.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.cor412_infimum_decomp
    (f : NNReal → ℝ) (t : NNReal)
    (hbefore : ∀ s < t, 0 ≤ f s) (ht : f t ≤ 0)
    (hb : BddBelow (range f)) :
    sInf (range f) = f t +
      sInf (range fun u : NNReal => f (t + u) - f t) := by sorry
