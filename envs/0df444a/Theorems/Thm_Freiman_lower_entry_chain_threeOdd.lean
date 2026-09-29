-- Prove2me | Theorems.Thm_Freiman_lower_entry_chain_threeOdd
-- name    : Freiman.lower_entry_chain_threeOdd
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:28.350235+00:00
-- url     : https://prove2.me/theorems/b58b0be0-1ffa-460b-bfee-a9f1580f3f76
-- title:
--   Freiman lower construction: entry chain threeOdd
-- statement:
--   Glue the six displayed core intervals in the exact source order, using only five adjacent contacts and the H endpoints. Odd classes reverse the order; the terminal2 exception changes the first core endpoint.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_chain_threeOdd (p : LowerPair) (hc : lowerEntryContext .threeOdd p)
    (hr : lowerEntryRowsHold p (lowerEntryContactRows .threeOdd))
    (hcore : ∀ l ∈ lowerEntryLabels, (lowerEntryCore .threeOdd p l).Nonempty ∧
      lowerEntryCore .threeOdd p l ⊆ lowerCover (lowerChild p l)) :
    lowerEntryH .threeOdd p ⊆ {t | ∃ l ∈ lowerEntryLabels, t ∈ lowerCover (lowerChild p l)} := by
  sorry
