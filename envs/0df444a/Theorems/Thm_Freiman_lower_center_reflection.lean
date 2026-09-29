-- Prove2me | Theorems.Thm_Freiman_lower_center_reflection
-- name    : Freiman.lower_center_reflection
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:05.002684+00:00
-- url     : https://prove2.me/theorems/1ae220c2-338e-4dfd-90cd-0b31a9f65d4e
-- title:
--   Freiman lower construction: center reflection
-- statement:
--   At the distinguished center, reflection swaps the two actual cfValue tails and keeps the central digit, so the central value is unchanged.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/foundations.tex, local values and reflection

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_center_reflection (a : ℤ → ℕ+) : localValue (fun i : ℤ => a (-i)) 0 = localValue a 0 := by
  sorry
