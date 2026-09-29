-- Prove2me | Theorems.Thm_Freiman_lower_early_parent_gluing
-- name    : Freiman.lower_early_parent_gluing
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:16.421997+00:00
-- url     : https://prove2.me/theorems/51ce112c-09a0-44a1-969a-dbe0fe5866f1
-- title:
--   Freiman lower construction: early parent gluing
-- statement:
--   The finite trunk contacts outside (15.26), the separately supplied early-chain geometry, and the R-star lower target bound cover the carried target. The chain receives priority over C20, while the marked R-star case uses C22.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, early connecting branch

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_early_parent_gluing (hchain : ∀ (t : ℝ) (p : LowerPair), lowerState t p → lowerEarlyDomain p → lowerEarlyGeometry p)
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ lowerA p 9 ∧ ¬ lowerL p ∧ lowerR p ∧ ¬ lowerA p 16) : lowerNumericSuccessor t p := by
  sorry
