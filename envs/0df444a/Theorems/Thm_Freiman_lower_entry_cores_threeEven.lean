-- Prove2me | Theorems.Thm_Freiman_lower_entry_cores_threeEven
-- name    : Freiman.lower_entry_cores_threeEven
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:19.757221+00:00
-- url     : https://prove2.me/theorems/a8903256-5d2d-45e7-a17e-61f16d39d7fd
-- title:
--   Freiman lower construction: entry cores threeEven
-- statement:
--   Finite actual endpoint-case adapter for the six explicit cores in class threeEven. The23 supplied comparisons include all exact periodic-compression equalities and all strict core nonemptiness checks.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_cores_threeEven (p : LowerPair) (hc : lowerEntryContext .threeEven p) (hd : lowerEntryDomain p)
    (ho : lowerEntryChildOrientation p) (hr : lowerEntryRowsHold p (lowerEntryCoreRows .threeEven)) :
    ∀ l ∈ lowerEntryLabels, (lowerEntryCore .threeEven p l).Nonempty ∧
      lowerEntryCore .threeEven p l ⊆ lowerCover (lowerChild p l) := by
  sorry
