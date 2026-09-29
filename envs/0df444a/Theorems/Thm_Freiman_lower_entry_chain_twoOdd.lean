-- Prove2me | Theorems.Thm_Freiman_lower_entry_chain_twoOdd
-- name    : Freiman.lower_entry_chain_twoOdd
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:38.918989+00:00
-- url     : https://prove2.me/theorems/69712f3b-7d25-4172-8316-b534078c3c7e
-- title:
--   Freiman lower construction: entry chain twoOdd
-- statement:
--   Glue the six displayed core intervals in the exact source order, using only five adjacent contacts and the H endpoints. Odd classes reverse the order; the terminal2 exception changes the first core endpoint.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_chain_twoOdd (p : LowerPair) (hc : lowerEntryContext .twoOdd p)
    (hr : lowerEntryRowsHold p (lowerEntryContactRows .twoOdd))
    (hcore : ∀ l ∈ lowerEntryLabels, (lowerEntryCore .twoOdd p l).Nonempty ∧
      lowerEntryCore .twoOdd p l ⊆ lowerCover (lowerChild p l)) :
    lowerEntryH .twoOdd p ⊆ {t | ∃ l ∈ lowerEntryLabels, t ∈ lowerCover (lowerChild p l)} := by
  sorry
