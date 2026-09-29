-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_state2_pairs_300_400
-- name    : Freiman.lowerEarlyTerminal_state2_pairs_300_400
-- status  : Proved
-- author  : @tp
-- created : 2026-09-13T20:51:42.679669+00:00
-- url     : https://prove2.me/theorems/99c62d77-3743-4a46-bca7-9c003f1a6a81
-- title:
--   Freiman H5: State2 pair certificates 301–400
-- statement:
--   Every pair certificate in positions 301 through 400 of the existing State2 early-terminal catalogue is valid: its bound identifiers are in range, and its exact Bernstein coefficient certificate proves the required exclusion on the catalogue rectangle. This consecutive batch is part of the full catalogue verification required by the H5 exception-anchor proof. The predicate and the catalogue data are unchanged. A bounded verification batch is used because the full catalogue exceeded the verifier's per-submission time limit.
-- source:
--   Freiman, Hall ray construction, Lemma 7.3 and condition (14.5); existing Prove2me prerequisite https://prove2.me/theorem/1aeb2eef-16e4-4e59-9044-9db9423807ee

import Definitions.Def_Freiman_lowerEarlyTerminalDataState2
import Mathlib.Data.Fintype.Basic
open Freiman

theorem Freiman.lowerEarlyTerminal_state2_pairs_300_400 : ∀ p ∈ (lowerEarlyTerminalState2.pairs.drop 300).take 100, lowerEarlyTerminalPairValid lowerEarlyTerminalState2 p := by sorry
