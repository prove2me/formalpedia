-- Prove2me | Theorems.Thm_Freiman_lower_bridge_C_comparison
-- name    : Freiman.lower_bridge_C_comparison
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:59:47.513295+00:00
-- url     : https://prove2.me/theorems/681b8888-fc0d-492a-b3c6-2c18c14825fa
-- title:
--   Freiman marked initial bridges: C comparison
-- statement:
--   Two signed C common-prefix contacts, the inner bound for the shortened 12/12 endpoint, and exact matrix-word reassociation place the whole strip in the earlier B family.
-- source:
--   Freiman report, initial_bridges.tex, corrected marked H entries; H_entry_bridges.json 185 exact polynomial records.

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_bridge_C_comparison (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hf : lowerBridgeFamily c = .C) (h : lowerBridgeFacts c n k) : lowerBridgeInterval .C n k 0 ⊆ lowerFamilyH .B n (k+2) 0 := by
  sorry
