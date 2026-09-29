-- Prove2me | Theorems.Thm_Freiman_lower_entry_aux_domain
-- name    : Freiman.lower_entry_aux_domain
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:00.857325+00:00
-- url     : https://prove2.me/theorems/c6c9375e-4407-4b59-bd53-6f94b7d2bc79
-- title:
--   Freiman lower construction: entry aux domain
-- statement:
--   (n k p : ℕ) : lowerEntryDomain (lowerNormalize (lowerFamilyPair .auxB n k p))
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_aux_domain (n k p : ℕ) : lowerEntryDomain (lowerNormalize (lowerFamilyPair .auxB n k p)) := by
  sorry
