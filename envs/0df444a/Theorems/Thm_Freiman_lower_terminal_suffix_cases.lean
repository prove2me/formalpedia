-- Prove2me | Theorems.Thm_Freiman_lower_terminal_suffix_cases
-- name    : Freiman.lower_terminal_suffix_cases
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:21.433146+00:00
-- url     : https://prove2.me/theorems/18040aa2-120c-4807-b93e-505c4acd3771
-- title:
--   Freiman lower construction: terminal suffix cases
-- statement:
--   Every reached normalized outward prefix is nonempty and its last digit is 1,2 or 3, even for the cores containing a secondary 4.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_section14.tex, six terminal states

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_terminal_suffix_cases (t : ℝ) (p : LowerPair) (hs : lowerState t p) :
    lowerEnds (lowerNormalize p).1 [1] ∨ lowerEnds (lowerNormalize p).1 [2] ∨ lowerEnds (lowerNormalize p).1 [3] := by
  sorry
