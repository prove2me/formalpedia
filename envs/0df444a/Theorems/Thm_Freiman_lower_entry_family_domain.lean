-- Prove2me | Theorems.Thm_Freiman_lower_entry_family_domain
-- name    : Freiman.lower_entry_family_domain
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:08.510791+00:00
-- url     : https://prove2.me/theorems/4d1fa599-285b-4ef9-8220-025c76553b5a
-- title:
--   Freiman lower construction: entry family domain
-- statement:
--   (f : LowerInitialFamily) (n k p : ℕ) : lowerEntryDomain (lowerNormalize (lowerFamilyPair f n k p))
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_family_domain (f : LowerInitialFamily) (n k p : ℕ) : lowerEntryDomain (lowerNormalize (lowerFamilyPair f n k p)) := by
  sorry
