-- Prove2me | Theorems.Thm_Freiman_lower_terminal_state2
-- name    : Freiman.lower_terminal_state2
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:07.040392+00:00
-- url     : https://prove2.me/theorems/c2c6e524-1fd7-4dda-bfae-557df8239dab
-- title:
--   Freiman lower construction: terminal state2
-- statement:
--   The exact fifteen-cover terminal chain on inherited left state 2, with actual cut C40, the C46 branching contact, the final union test and inherited A9. This explicitly keeps states 1 and 2 distinct from the narrower state-3 rectangle.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_133_139.tex, prop:l139; lower_120_132.tex, s15:terminal-extension

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_terminal_state2 (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p) (h27 : ¬ lowerA p 27) (h34 : ¬ lowerA p 34)
    (he : lowerEnds (lowerNormalize p).1 [2]) : lowerEarlyGeometry p := by
  sorry
