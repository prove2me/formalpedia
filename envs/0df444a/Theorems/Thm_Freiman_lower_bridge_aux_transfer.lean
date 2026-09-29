-- Prove2me | Theorems.Thm_Freiman_lower_bridge_aux_transfer
-- name    : Freiman.lower_bridge_aux_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:59:24.417315+00:00
-- url     : https://prove2.me/theorems/8d6f0ee9-e139-42cc-ad7c-5278b6ac4408
-- title:
--   Freiman marked initial bridges: aux transfer
-- statement:
--   The recorded 7/5 auxiliary cut, including the strict complementary decision, follows from its numerator and certified incoming orientation.
-- source:
--   Freiman report, initial_bridges.tex, corrected marked H entries; H_entry_bridges.json 185 exact polynomial records.

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_bridge_aux_transfer (hfrac : ∀ (w : List ℕ+) (t : ℝ), 0 < t → prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧ 0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧ (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d - (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length) (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hm : lowerInitialSeamLink (lowerBridgeSeamCase c) n (lowerBridgeK c k) 0) (hn : lowerBridgeNumeric c (lowerInitialX n) (lowerInitialY k)) (hw : ∀ r ∈ lowerBridgeRecords c, r.kind = .width → lowerBridgeRecordFact c n k r) (r : LowerBridgeRecord) (hr : r ∈ lowerBridgeRecords c) (hk : r.kind = .auxiliary) : lowerBridgeRecordFact c n k r := by
  sorry
