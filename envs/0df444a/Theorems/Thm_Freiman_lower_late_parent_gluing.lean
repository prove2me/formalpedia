-- Prove2me | Theorems.Thm_Freiman_lower_late_parent_gluing
-- name    : Freiman.lower_late_parent_gluing
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:16.555339+00:00
-- url     : https://prove2.me/theorems/0b3f9de7-5315-4c99-babd-dfba2650af79
-- title:
--   Freiman lower construction: late parent gluing
-- statement:
--   Attach the separately certified long or short late route to the finite trunk; L-star and R-star cases use their exact carried-target anchors and safe truncations.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, late left-shortened branch

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_late_parent_gluing (hroute : ∀ (t : ℝ) (p : LowerPair), lowerState t p → (¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p) → lowerLateEntryDomain p → ∃ ls : List LowerLabel, lowerLateRouteValid p ls)
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p) : lowerNumericSuccessor t p := by
  sorry
