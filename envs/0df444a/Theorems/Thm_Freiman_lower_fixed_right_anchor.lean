-- Prove2me | Theorems.Thm_Freiman_lower_fixed_right_anchor
-- name    : Freiman.lower_fixed_right_anchor
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:14:31.710692+00:00
-- url     : https://prove2.me/theorems/10b867c5-0b8a-45a1-9518-539f475a9a84
-- title:
--   Freiman lower construction: fixed right anchor
-- statement:
--   The fixed-root union reaches sqrt(21); its witness is an actual ordinary cover.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, fixed initial union upper anchor

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_fixed_right_anchor : Real.sqrt 21 ∈ lowerInitialSet := by
  sorry
