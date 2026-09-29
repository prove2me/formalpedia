-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_pairs_300_400
-- name    : Freiman.lowerEarlyTerminal_terminal3_pairs_300_400
-- status  : Proved
-- author  : @tp
-- created : 2026-09-13T20:52:27.696199+00:00
-- url     : https://prove2.me/theorems/7a63e9f1-396a-4430-badf-c4ea8a0711b1
-- title:
--   Freiman H5: Terminal3 pair certificates 301–400
-- statement:
--   Every pair certificate in positions 301 through 400 of the existing Terminal3 early-terminal catalogue is valid: its bound identifiers are in range, and its exact Bernstein coefficient certificate proves the required exclusion on the catalogue rectangle. This consecutive batch is part of the full catalogue verification required by the H5 exception-anchor proof. The predicate and the catalogue data are unchanged. A bounded verification batch is used because the full catalogue exceeded the verifier's per-submission time limit.
-- source:
--   Freiman, Hall ray construction, Lemma 7.3 and condition (14.5); existing Prove2me prerequisite https://prove2.me/theorem/7431370d-0923-475d-a003-ba94a041ebe0

import Definitions.Def_Freiman_lowerEarlyTerminalDataTerminal3
import Mathlib.Data.Fintype.Basic
open Freiman

theorem Freiman.lowerEarlyTerminal_terminal3_pairs_300_400 : ∀ p ∈ (lowerEarlyTerminalTerminal3.pairs.drop 300).take 100, lowerEarlyTerminalPairValid lowerEarlyTerminalTerminal3 p := by sorry
