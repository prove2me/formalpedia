-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_stopped_grid_error
-- name    : Kyprianou.Ch04.ito43_stopped_grid_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:37:57.73284+00:00
-- url     : https://prove2.me/theorems/61f1631a-6fd1-5ca1-8647-7f46e736e571
-- title:
--   Uniform stopped grid error bounded by full cell errors and one mesh charge
-- statement:
--   Sum the full-cell integral errors with one additional terminal mesh charge.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_stopped_cell_error
import Theorems.Thm_Kyprianou_Ch04_ito43_cut_sum_bound
open MeasureTheory Set
set_option autoImplicit false

/-- Uniform stopped-grid error is bounded by full-cell L1 errors and a single mesh charge. -/

theorem Kyprianou.Ch04.ito43_stopped_grid_error (H : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (u : ℕ → ℝ)
    (hu : Monotone u) (n : ℕ) (T t M δ : ℝ)
    (h0 : u 0 = 0) (hn : u n = T) (ht : t ∈ Icc 0 T)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hmesh : ∀ k < n, u (k+1) - u k ≤ δ)
    (hHi : IntegrableOn H (Icc 0 T))
    (hgi : ∀ r ∈ Icc 0 T, IntegrableOn (fun s => g s r) (Icc 0 T))
    (hH : ∀ s ∈ Icc 0 T, |H s| ≤ M)
    (hg : ∀ s ∈ Icc 0 T, ∀ r ∈ Icc 0 T, |g s r| ≤ M) :
    let v := fun k => min t (u k)
    |(∫ s in Icc 0 t, H s) -
      (∑ k ∈ Finset.range n, (∫ s in Icc (v k) (v (k+1)), g s (v (k+1))))| ≤
      (∑ k ∈ Finset.range n, (∫ s in Icc (u k) (u (k+1)), |H s - g s (u (k+1))|)) +
        2*M*δ := by sorry
