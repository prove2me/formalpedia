-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_state1_pairs_200_300
-- name    : Freiman.lowerEarlyTerminal_state1_pairs_200_300
-- status  : Proved
-- author  : @tp
-- created : 2026-09-13T20:51:03.973947+00:00
-- url     : https://prove2.me/theorems/a7638bae-dc71-4c4f-8662-7f08216b2301
-- title:
--   Freiman H5: State1 pair certificates 201–300
-- statement:
--   Every pair certificate in positions 201 through 300 of the existing State1 early-terminal catalogue is valid: its bound identifiers are in range, and its exact Bernstein coefficient certificate proves the required exclusion on the catalogue rectangle. This consecutive batch is part of the full catalogue verification required by the H5 exception-anchor proof. The predicate and the catalogue data are unchanged. A bounded verification batch is used because the full catalogue exceeded the verifier's per-submission time limit.
-- source:
--   Freiman, Hall ray construction, Lemma 7.3 and condition (14.5); existing Prove2me prerequisite https://prove2.me/theorem/5871c401-5f58-42d4-869c-bbd5f01c3fd9

import Definitions.Def_Freiman_lowerEarlyTerminalDataState1
import Mathlib.Data.Fintype.Basic
open Freiman

theorem Freiman.lowerEarlyTerminal_state1_pairs_200_300 : ∀ p ∈ (lowerEarlyTerminalState1.pairs.drop 200).take 100, lowerEarlyTerminalPairValid lowerEarlyTerminalState1 p := by sorry
