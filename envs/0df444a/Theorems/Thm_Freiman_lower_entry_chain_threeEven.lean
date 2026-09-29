-- Prove2me | Theorems.Thm_Freiman_lower_entry_chain_threeEven
-- name    : Freiman.lower_entry_chain_threeEven
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:32.446514+00:00
-- url     : https://prove2.me/theorems/9dee157f-edb4-407d-8a40-1dd5a25bd446
-- title:
--   Freiman lower construction: entry chain threeEven
-- statement:
--   Glue the six displayed core intervals in the exact source order, using only five adjacent contacts and the H endpoints. Odd classes reverse the order; the terminal2 exception changes the first core endpoint.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_chain_threeEven (p : LowerPair) (hc : lowerEntryContext .threeEven p)
    (hr : lowerEntryRowsHold p (lowerEntryContactRows .threeEven))
    (hcore : ∀ l ∈ lowerEntryLabels, (lowerEntryCore .threeEven p l).Nonempty ∧
      lowerEntryCore .threeEven p l ⊆ lowerCover (lowerChild p l)) :
    lowerEntryH .threeEven p ⊆ {t | ∃ l ∈ lowerEntryLabels, t ∈ lowerCover (lowerChild p l)} := by
  sorry
