-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_grid_telescope
-- name    : Kyprianou.Ch04.ito43_grid_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:45:40.502027+00:00
-- url     : https://prove2.me/theorems/e9f28bd3-c978-422c-b90b-2b20c7ac2213
-- title:
--   Exact stopped-grid two-variable time-space telescoping identity
-- statement:
--   Exact stopped-grid two-variable time-space telescoping identity.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
open scoped NNReal
set_option autoImplicit false

/-- Exact stopped-grid time/space decomposition of a two-variable increment. -/

theorem Kyprianou.Ch04.ito43_grid_telescope (X : NNReal → ℝ) (f : ℝ × ℝ → ℝ)
    (u : ℕ → NNReal) (n : ℕ) (t : NNReal) :
    f ((min t (u n) : NNReal), X (min t (u n))) -
      f ((min t (u 0) : NNReal), X (min t (u 0))) =
      (∑ k ∈ Finset.range n,
        (f ((min t (u (k+1)) : NNReal), X (min t (u (k+1)))) -
          f ((min t (u k) : NNReal), X (min t (u (k+1)))))) +
      (∑ k ∈ Finset.range n,
        (f ((min t (u k) : NNReal), X (min t (u (k+1)))) -
          f ((min t (u k) : NNReal), X (min t (u k))))) := by sorry
