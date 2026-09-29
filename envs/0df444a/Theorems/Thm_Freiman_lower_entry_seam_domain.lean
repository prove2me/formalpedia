-- Prove2me | Theorems.Thm_Freiman_lower_entry_seam_domain
-- name    : Freiman.lower_entry_seam_domain
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:00.898737+00:00
-- url     : https://prove2.me/theorems/e9ad24a1-4f0a-4e51-9afc-c11662e86f0d
-- title:
--   Freiman lower construction: entry seam domain
-- statement:
--   (c : LowerInitialSeamCase) (n k p : ℕ) (hc : lowerInitialSeamZero c = decide (n=0)) :
--       lowerEntryDomain (lowerNormalize (lowerFamilyPair (lowerInitialSeamFamily c) n k p))
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_seam_domain (c : LowerInitialSeamCase) (n k p : ℕ) (hc : lowerInitialSeamZero c = decide (n=0)) :
    lowerEntryDomain (lowerNormalize (lowerFamilyPair (lowerInitialSeamFamily c) n k p)) := by
  sorry
