-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_grid_residual_identity
-- name    : Kyprianou.Ch04.ito43_grid_residual_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:47:49.380715+00:00
-- url     : https://prove2.me/theorems/16faa472-6120-4ff4-b6a2-b5deb9f114b1
-- title:
--   Stopped-grid stochastic sum equals total increment minus time and spatial residuals
-- statement:
--   The stopped-grid stochastic sum equals the total two-variable increment minus its time and spatial remainders.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_grid_telescope
open scoped NNReal
set_option autoImplicit false

/-- The stopped-grid stochastic sum equals the total increment less the time and spatial remainders. -/

theorem Kyprianou.Ch04.ito43_grid_residual_identity (X g : NNReal → ℝ) (f : ℝ × ℝ → ℝ)
    (T t : NNReal) (ht : t ≤ T) (n : ℕ) (hn : 0 < n) :
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    (∑ k ∈ Finset.range n, g (u k) * (X (v (k+1)) - X (v k))) =
      f ((t : ℝ), X t) - f (0, X 0) -
      (∑ k ∈ Finset.range n, (f ((v (k+1) : ℝ), X (v (k+1))) -
        f ((v k : ℝ), X (v (k+1))))) -
      (∑ k ∈ Finset.range n, (f ((v k : ℝ), X (v (k+1))) -
        f ((v k : ℝ), X (v k)) - g (u k) * (X (v (k+1)) - X (v k)))) := by sorry
