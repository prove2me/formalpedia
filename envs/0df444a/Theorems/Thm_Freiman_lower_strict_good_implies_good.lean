-- Prove2me | Theorems.Thm_Freiman_lower_strict_good_implies_good
-- name    : Freiman.lower_strict_good_implies_good
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:41.254315+00:00
-- url     : https://prove2.me/theorems/6210d224-e1f3-4d1c-b053-5d0b4ae5f948
-- title:
--   Freiman lower construction: strict good implies good
-- statement:
--   Strict overlap of the two actual closed fork intervals implies nonempty overlap.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_strict_good_implies_good (p : LowerPair) (h : lowerStrictGood p) : lowerGood p := by
  sorry
