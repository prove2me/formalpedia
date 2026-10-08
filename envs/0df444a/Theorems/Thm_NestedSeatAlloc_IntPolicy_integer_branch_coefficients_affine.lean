-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_integer_branch_coefficients_affine
-- name    : NestedSeatAlloc.IntPolicy.integer_branch_coefficients_affine
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T16:24:30.424685+00:00
-- url     : https://prove2.me/theorems/8578c7a0-f455-4b64-a03f-6c4801cd1b57
-- title:
--   Integer-demand branch coefficients give the equation-27 affine form
-- statement:
--   For integer-valued demand, the scaled truncation is represented on each unit interval by the constant-tail coefficient plus the strict-tail slope coefficient.
-- source:
--   Source-faithful pointwise coefficient identity in candidates/eq27_integer_branch_coefficients_affine.lean; it is the exact c_m/d_m premise for the final expected-revenue affine assembly.

import Mathlib

namespace NestedSeatAlloc.IntPolicy

theorem integer_branch_coefficients_affine
    (a x : ℝ) (m : ℕ) (hx : ∃ n : ℕ, x = n) :
    ∀ s ∈ Set.Icc (m : ℝ) (m + 1),
      a * min s x =
        (if x ≤ (m : ℝ) then a * x else 0) +
          (if (m : ℝ) < x then a else 0) * s := by sorry

end NestedSeatAlloc.IntPolicy
