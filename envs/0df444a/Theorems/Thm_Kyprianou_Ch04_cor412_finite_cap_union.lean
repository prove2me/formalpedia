-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_finite_cap_union
-- name    : Kyprianou.Ch04.cor412_finite_cap_union
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:22:26.78834+00:00
-- url     : https://prove2.me/theorems/cea93759-0abf-4932-8319-af173dcf2e8b
-- title:
--   Integer caps exhaust the finite extended clock event
-- statement:
--   Integer caps exhaust the finite extended clock event.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The increasing finite integer caps exhaust the finite extended-clock event. -/

theorem Kyprianou.Ch04.cor412_finite_cap_union
    {Ω : Type} (τ : Ω → WithTop NNReal) :
    (⋃ n : ℕ, {w : Ω | τ w ≤ ((n : NNReal) : WithTop NNReal)}) =
      {w : Ω | τ w ≠ ⊤} := by sorry
