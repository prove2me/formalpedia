-- Prove2me | Theorems.Thm_Freiman_lower_entry_goodness_twoOdd
-- name    : Freiman.lower_entry_goodness_twoOdd
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:25.987273+00:00
-- url     : https://prove2.me/theorems/575aed87-6ebe-48de-806f-60685b8172fe
-- title:
--   Freiman lower construction: entry goodness twoOdd
-- statement:
--   Finite actual endpoint-case adapter for the six twoOdd children. It uses both defining fork contacts, known child orientation and the explicit virtualNN exception; all numeric comparisons are the supplied source rows.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_goodness_twoOdd (p : LowerPair) (hc : lowerEntryContext .twoOdd p) (hd : lowerEntryDomain p)
    (ho : lowerEntryChildOrientation p) (hv : lowerEntryVirtualNN p)
    (hr : lowerEntryRowsHold p (lowerEntryGoodRows .twoOdd)) :
    ∀ l ∈ lowerEntryLabels, lowerStrictGood (lowerChild p l) := by
  sorry
