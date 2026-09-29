-- Prove2me | Theorems.Thm_Freiman_lower_entry_good_parities
-- name    : Freiman.lower_entry_good_parities
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:37.040045+00:00
-- url     : https://prove2.me/theorems/5628dfd4-b209-4bd9-bb42-3460fc9c8103
-- title:
--   Freiman lower construction: entry good parities
-- statement:
--   Finite row inventory: all listed row parities agree with the actual terminal class. This is a small closed-list check, separated from interval arithmetic.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_good_parities (c : LowerEntryClass) (p : LowerPair) (hc : lowerEntryContext c p)
    (e : LowerEntryRow) (he : e ∈ lowerEntryGoodRows c) :
    p.1.length % 2 = e.parity % 2 ∧ p.2.length % 2 = e.parity % 2 := by
  sorry
