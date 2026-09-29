-- Prove2me | Theorems.Thm_Freiman_lower_entry_cores_threeOdd
-- name    : Freiman.lower_entry_cores_threeOdd
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:35.278981+00:00
-- url     : https://prove2.me/theorems/b1a8679c-9b71-4566-afd4-35e04d9c9f89
-- title:
--   Freiman lower construction: entry cores threeOdd
-- statement:
--   Finite actual endpoint-case adapter for the six explicit cores in class threeOdd. The23 supplied comparisons include all exact periodic-compression equalities and all strict core nonemptiness checks.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_cores_threeOdd (p : LowerPair) (hc : lowerEntryContext .threeOdd p) (hd : lowerEntryDomain p)
    (ho : lowerEntryChildOrientation p) (hr : lowerEntryRowsHold p (lowerEntryCoreRows .threeOdd)) :
    ∀ l ∈ lowerEntryLabels, (lowerEntryCore .threeOdd p l).Nonempty ∧
      lowerEntryCore .threeOdd p l ⊆ lowerCover (lowerChild p l) := by
  sorry
