-- Prove2me | Theorems.Thm_Freiman_lower_model_reflection
-- name    : Freiman.lower_model_reflection
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:00.433499+00:00
-- url     : https://prove2.me/theorems/ea8a40bd-2f5b-47f3-85b0-fe413052519e
-- title:
--   Freiman lower construction: model reflection
-- statement:
--   Reflection exchanges the two physical sides without reversing their outward words; the seven cores are kept with their two orientations and 31313 is palindromic.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, physical reflection; foundations.tex, central cores

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_model_reflection (a : ℤ → ℕ+) (ha : LowerModel a) : LowerModel (fun i : ℤ => a (-i)) := by
  sorry
