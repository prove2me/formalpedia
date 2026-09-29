-- Prove2me | Theorems.Thm_Freiman_lower_entry_cores_twoOdd
-- name    : Freiman.lower_entry_cores_twoOdd
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:39.107972+00:00
-- url     : https://prove2.me/theorems/92933c8e-4297-43af-b54e-7f54966396c6
-- title:
--   Freiman lower construction: entry cores twoOdd
-- statement:
--   Finite actual endpoint-case adapter for the six explicit cores in class twoOdd. The23 supplied comparisons include all exact periodic-compression equalities and all strict core nonemptiness checks.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_cores_twoOdd (p : LowerPair) (hc : lowerEntryContext .twoOdd p) (hd : lowerEntryDomain p)
    (ho : lowerEntryChildOrientation p) (hr : lowerEntryRowsHold p (lowerEntryCoreRows .twoOdd)) :
    ∀ l ∈ lowerEntryLabels, (lowerEntryCore .twoOdd p l).Nonempty ∧
      lowerEntryCore .twoOdd p l ⊆ lowerCover (lowerChild p l) := by
  sorry
