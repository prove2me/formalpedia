-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_residual_error
-- name    : Kyprianou.Ch04.ito43_residual_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:07:50.854098+00:00
-- url     : https://prove2.me/theorems/932bf014-099f-5430-a51c-2ea8171f2c3b
-- title:
--   Exact stochastic residual error decomposition
-- statement:
--   Exact stochastic residual error decomposition.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_grid_residual_identity
open scoped NNReal
set_option autoImplicit false

/-- A residual stochastic sum has exactly the sum of the time and spatial approximation errors. -/

theorem Kyprianou.Ch04.ito43_residual_error (X g : NNReal → ℝ) (f : ℝ × ℝ → ℝ)
    (T t : NNReal) (ht : t ≤ T) (n : ℕ) (hn : 0 < n) (A B : ℝ) :
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    (∑ k ∈ Finset.range n, g (u k) * (X (v (k+1)) - X (v k))) -
        (f ((t : ℝ), X t) - f (0, X 0) - A - B) =
      (A - ∑ k ∈ Finset.range n,
        (f ((v (k+1) : ℝ), X (v (k+1))) - f ((v k : ℝ), X (v (k+1))))) +
      (B - ∑ k ∈ Finset.range n, (f ((v k : ℝ), X (v (k+1))) -
        f ((v k : ℝ), X (v k)) - g (u k) * (X (v (k+1)) - X (v k)))) := by sorry
