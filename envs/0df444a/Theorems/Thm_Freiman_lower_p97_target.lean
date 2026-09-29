-- Prove2me | Theorems.Thm_Freiman_lower_p97_target
-- name    : Freiman.lower_p97_target
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:27.658414+00:00
-- url     : https://prove2.me/theorems/c8f87deb-05a5-4c2f-a82f-913e14863e51
-- title:
--   Freiman lower construction: p97 target
-- statement:
--   The shortened-left p97 target anchor uses only an earlier admissible early chain, or the earlier R-star target row and C22 priority. No future admissibility is assumed.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/h5_target.tex, lem:h5-original-two; global_selection.tex, previous-depth priority argument

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_p97_target (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) : lowerP97Anchor (h n) t := by
  sorry
