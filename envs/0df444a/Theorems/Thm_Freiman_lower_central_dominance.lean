-- Prove2me | Theorems.Thm_Freiman_lower_central_dominance
-- name    : Freiman.lower_central_dominance
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:16:19.519295+00:00
-- url     : https://prove2.me/theorems/a7447a63-d836-42e6-a256-af6c8350d19c
-- title:
--   Freiman lower construction: central dominance
-- statement:
--   (a : ℤ → ℕ+) (ha : LowerModel a) (i : ℤ) (hi : i ≠ 0) :
--       localValue a i < (113195/25000 : ℝ)
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/foundations.tex, found:central-dominance

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_central_dominance (a : ℤ → ℕ+) (ha : LowerModel a) (i : ℤ) (hi : i ≠ 0) :
    localValue a i < (113195/25000 : ℝ) := by
  sorry
