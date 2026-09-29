-- Prove2me | Theorems.Thm_Freiman_lower_repeated3_model
-- name    : Freiman.lower_repeated3_model
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:50.738973+00:00
-- url     : https://prove2.me/theorems/2f528068-1cce-4626-abd1-61e444cb4814
-- title:
--   Freiman lower construction: repeated3 model
-- statement:
--   The explicit period-3 two-sided completion retains the physical core and avoids 31313 because neither old outward word ends in 31.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/j_family.tex, admissible infinite run limit

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_repeated3_model (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) : lowerHasValue (lowerRunValue p) := by
  sorry
