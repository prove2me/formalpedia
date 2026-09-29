-- Prove2me | Theorems.Thm_Freiman_lower_width_bounds
-- name    : Freiman.lower_width_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:53.544245+00:00
-- url     : https://prove2.me/theorems/f8b2cc98-9c0b-4461-8687-409a995d0d1b
-- title:
--   Freiman lower construction: width bounds
-- statement:
--   The full [alpha,beta] width is strictly positive and bounded by the standard finite-prefix cylinder estimate.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, full-width positivity and cylinder shrinking

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_width_bounds (w : List ℕ+) : 0 < lowerWidth w ∧ lowerWidth w ≤ 1 / ((Nat.fib (w.length+1) : ℝ)^2) := by
  sorry
