-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_pairs_200_300
-- name    : Freiman.lowerEarlyTerminal_terminal3_pairs_200_300
-- status  : Proved
-- author  : @tp
-- created : 2026-09-13T20:52:24.264465+00:00
-- url     : https://prove2.me/theorems/7f5c8acd-1804-4518-9d7d-599f81c75794
-- title:
--   Freiman H5: Terminal3 pair certificates 201–300
-- statement:
--   Every pair certificate in positions 201 through 300 of the existing Terminal3 early-terminal catalogue is valid: its bound identifiers are in range, and its exact Bernstein coefficient certificate proves the required exclusion on the catalogue rectangle. This consecutive batch is part of the full catalogue verification required by the H5 exception-anchor proof. The predicate and the catalogue data are unchanged. A bounded verification batch is used because the full catalogue exceeded the verifier's per-submission time limit.
-- source:
--   Freiman, Hall ray construction, Lemma 7.3 and condition (14.5); existing Prove2me prerequisite https://prove2.me/theorem/7431370d-0923-475d-a003-ba94a041ebe0

import Definitions.Def_Freiman_lowerEarlyTerminalDataTerminal3
import Mathlib.Data.Fintype.Basic
open Freiman

theorem Freiman.lowerEarlyTerminal_terminal3_pairs_200_300 : ∀ p ∈ (lowerEarlyTerminalTerminal3.pairs.drop 200).take 100, lowerEarlyTerminalPairValid lowerEarlyTerminalTerminal3 p := by sorry
