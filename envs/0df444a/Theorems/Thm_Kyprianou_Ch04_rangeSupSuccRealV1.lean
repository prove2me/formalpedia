-- Prove2me | Theorems.Thm_Kyprianou_Ch04_rangeSupSuccRealV1
-- name    : Kyprianou.Ch04.rangeSupSuccRealV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:39:23.651275+00:00
-- url     : https://prove2.me/theorems/59b34395-cda8-4ff6-b6df-eacda0150e0c
-- title:
--   rangeSupSuccRealV1
-- statement:
--   Successor decomposition of the finite prefix supremum.
-- source:
--   Kyprianou (2006), Exercise 4.5 supporting finite maximal inequality

import Mathlib
set_option autoImplicit false

theorem Kyprianou.Ch04.rangeSupSuccRealV1 (a : ℕ → ℝ) (n : ℕ) :
    (Finset.range (n+1+1)).sup' Finset.nonempty_range_add_one a =
      a (n+1) ⊔ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one a := by
  sorry
