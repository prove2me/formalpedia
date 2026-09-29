-- Prove2me | Theorems.Thm_Freiman_lower_entry_goodness_threeEven
-- name    : Freiman.lower_entry_goodness_threeEven
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:17.10397+00:00
-- url     : https://prove2.me/theorems/9bd71527-7752-4264-951b-511b779c6122
-- title:
--   Freiman lower construction: entry goodness threeEven
-- statement:
--   Finite actual endpoint-case adapter for the six threeEven children. It uses both defining fork contacts, known child orientation and the explicit virtualNN exception; all numeric comparisons are the supplied source rows.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_goodness_threeEven (p : LowerPair) (hc : lowerEntryContext .threeEven p) (hd : lowerEntryDomain p)
    (ho : lowerEntryChildOrientation p) (hv : lowerEntryVirtualNN p)
    (hr : lowerEntryRowsHold p (lowerEntryGoodRows .threeEven)) :
    ∀ l ∈ lowerEntryLabels, lowerStrictGood (lowerChild p l) := by
  sorry
