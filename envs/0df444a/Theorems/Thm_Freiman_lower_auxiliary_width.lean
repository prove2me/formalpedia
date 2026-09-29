-- Prove2me | Theorems.Thm_Freiman_lower_auxiliary_width
-- name    : Freiman.lower_auxiliary_width
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:14:32.9166+00:00
-- url     : https://prove2.me/theorems/170afb7a-664d-49de-b067-5a61b3f7d28c
-- title:
--   Freiman lower construction: auxiliary width
-- statement:
--   The two descriptions of the 13 auxiliary width agree exactly.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, endpoint rules

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_auxiliary_width (w : List ℕ+) : |prefixEval w lowerBeta - prefixEval (w ++ [1,3]) lowerAlpha| = lowerWidth (w ++ [1,3]) := by
  sorry
