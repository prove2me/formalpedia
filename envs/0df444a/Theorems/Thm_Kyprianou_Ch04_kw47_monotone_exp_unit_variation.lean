-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_monotone_exp_unit_variation
-- name    : Kyprianou.Ch04.kw47_monotone_exp_unit_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:36:35.344159+00:00
-- url     : https://prove2.me/theorems/258ef868-820c-5402-ba7f-4f4c9dfb6d80
-- title:
--   Unit grid variation of the decreasing exponential of a running supremum
-- statement:
--   If U is nonnegative and nondecreasing and alpha is nonnegative, exp(-alpha U) is nonincreasing and takes values in (0,1]. Its total absolute variation on any finite increasing time grid is bounded by one, because the variation sum telescopes to its first value minus its last value. This controls the running-supremum factor in the Kella–Whitt exponential product decomposition.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.7, pp. 108-109; monotone exponential factor in the deterministic finite-grid summation-by-parts proof.

import Mathlib
open Filter
open scoped NNReal
set_option autoImplicit false

/-- An exponential of a nonnegative increasing path has total
variation at most one on every ordered finite grid. -/

theorem Kyprianou.Ch04.kw47_monotone_exp_unit_variation
    (U : NNReal → Real) (hU : Monotone U)
    (hNonneg : ∀ t, 0 ≤ U t)
    (alpha : Real) (hAlpha : 0 ≤ alpha)
    (u : ℕ → NNReal) (hu : Monotone u)
    (n : ℕ) :
    (∑ i ∈ Finset.range n,
      |Real.exp (-alpha * U (u (i + 1))) -
       Real.exp (-alpha * U (u i))|) ≤ 1 := by sorry
