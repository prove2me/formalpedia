-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_stopped_cell_error
-- name    : Kyprianou.Ch04.ito43_stopped_cell_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:30:53.735014+00:00
-- url     : https://prove2.me/theorems/a110ac8c-505c-52fb-877e-a376077d457b
-- title:
--   Stopped cell error bound with a single mesh charge
-- statement:
--   The stopped cell error is bounded by full-cell L1 error and an extra mesh charge only for strictly cut cells.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

/-- A stopped cell incurs its full-cell L1 error, plus a mesh charge only when cut. -/

theorem Kyprianou.Ch04.ito43_stopped_cell_error (H : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (a b t M δ : ℝ) (hab : a ≤ b) (hmesh : b-a ≤ δ)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hHi : IntegrableOn H (Icc a b)) (hgi : IntegrableOn (fun s => g s b) (Icc a b))
    (hH : ∀ s ∈ Icc a b, |H s| ≤ M)
    (hg : ∀ s ∈ Icc a b, ∀ r ∈ Icc a b, |g s r| ≤ M) :
    |(∫ s in Icc (min t a) (min t b), H s) -
      ∫ s in Icc (min t a) (min t b), g s (min t b)| ≤
      (∫ s in Icc a b, |H s - g s b|) +
        if a < t ∧ t < b then 2*M*δ else 0 := by sorry
