-- Prove2me | Theorems.Thm_Freiman_lower_geometry_equal_large_plain_with_run
-- name    : Freiman.lower_geometry_equal_large_plain_with_run
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:57.525961+00:00
-- url     : https://prove2.me/theorems/914efbe7-00ee-4f7e-bd98-b3248da3447b
-- title:
--   Freiman lower construction: geometry equal large plain with run
-- statement:
--   The finite trunk supplies all ordinary contacts and both outer anchors; when its J2/J1 interface is present, the separately supplied complete repeated3 family fills precisely that interval. Safe suffix-target truncations and priorities are retained.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_120_132.tex, finite trunk and optional J interface; j_family.tex

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_geometry_equal_large_plain_with_run (hJ : ∀ (t : ℝ) (p : LowerPair), lowerState t p → lowerRunOffered p → lowerRunFamily p)
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ ¬ lowerL p) : lowerNumericSuccessor t p := by
  sorry
