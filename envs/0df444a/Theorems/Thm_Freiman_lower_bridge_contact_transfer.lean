-- Prove2me | Theorems.Thm_Freiman_lower_bridge_contact_transfer
-- name    : Freiman.lower_bridge_contact_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:59:27.838558+00:00
-- url     : https://prove2.me/theorems/ddb76f01-30bc-4a30-8297-60aa16bd5ff7
-- title:
--   Freiman marked initial bridges: contact transfer
-- statement:
--   Actual signed prefix-difference formula for the recorded contacts. C uses its two common prefixes with opposite determinant signs.
-- source:
--   Freiman report, initial_bridges.tex, corrected marked H entries; H_entry_bridges.json 185 exact polynomial records.

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_bridge_contact_transfer (hfrac : ∀ (w : List ℕ+) (t : ℝ), 0 < t → prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧ 0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧ (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d - (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length) (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hm : lowerInitialSeamLink (lowerBridgeSeamCase c) n (lowerBridgeK c k) 0) (hn : lowerBridgeNumeric c (lowerInitialX n) (lowerInitialY k)) (r : LowerBridgeRecord) (hr : r ∈ lowerBridgeRecords c) (hk : r.kind ≠ .width ∧ r.kind ≠ .auxiliary ∧ r.kind ≠ .h7 ∧ r.kind ≠ .notA9) : lowerBridgeRecordFact c n k r := by
  sorry
