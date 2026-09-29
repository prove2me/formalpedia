-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_pairs_400_500
-- name    : Freiman.lowerEarlyTerminal_terminal3_pairs_400_500
-- status  : Proved
-- author  : @tp
-- created : 2026-09-13T20:52:30.312589+00:00
-- url     : https://prove2.me/theorems/8bc1f8d5-984f-4f9e-860a-9cf668ddd7d2
-- title:
--   Freiman H5: Terminal3 pair certificates 401–500
-- statement:
--   Every pair certificate in positions 401 through 500 of the existing Terminal3 early-terminal catalogue is valid: its bound identifiers are in range, and its exact Bernstein coefficient certificate proves the required exclusion on the catalogue rectangle. This consecutive batch is part of the full catalogue verification required by the H5 exception-anchor proof. The predicate and the catalogue data are unchanged. A bounded verification batch is used because the full catalogue exceeded the verifier's per-submission time limit.
-- source:
--   Freiman, Hall ray construction, Lemma 7.3 and condition (14.5); existing Prove2me prerequisite https://prove2.me/theorem/7431370d-0923-475d-a003-ba94a041ebe0

import Definitions.Def_Freiman_lowerEarlyTerminalDataTerminal3
import Mathlib.Data.Fintype.Basic
open Freiman

theorem Freiman.lowerEarlyTerminal_terminal3_pairs_400_500 : ∀ p ∈ (lowerEarlyTerminalTerminal3.pairs.drop 400).take 100, lowerEarlyTerminalPairValid lowerEarlyTerminalTerminal3 p := by sorry
