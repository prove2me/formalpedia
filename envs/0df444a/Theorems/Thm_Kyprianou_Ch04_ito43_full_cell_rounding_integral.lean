-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_full_cell_rounding_integral
-- name    : Kyprianou.Ch04.ito43_full_cell_rounding_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:46:43.925292+00:00
-- url     : https://prove2.me/theorems/18ef1bbe-a37b-465f-beda-f19918d7811a
-- title:
--   Full cell integrals equal the integral of the ceiling-rounded kernel
-- statement:
--   The sum of full-cell integrals equals the right-rounded kernel integral.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_ceiling_cell
open MeasureTheory Set
set_option autoImplicit false

/-- Full cell integrals equal the integral evaluated at the right rounded time. -/

theorem Kyprianou.Ch04.ito43_full_cell_rounding_integral (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 0 < n) (F : ℝ → ℝ → ℝ)
    (hI : IntegrableOn (fun s => F s (T * (Nat.ceil (s * (n : ℝ) / T) : ℝ) / (n : ℝ)))
      (Icc 0 T)) :
    let u : ℕ → ℝ := fun k => T * (k : ℝ) / (n : ℝ)
    (∑ k ∈ Finset.range n, (∫ s in Icc (u k) (u (k+1)), F s (u (k+1)))) =
      ∫ s in Icc 0 T, F s (T * (Nat.ceil (s * (n : ℝ) / T) : ℝ) / (n : ℝ)) := by sorry
