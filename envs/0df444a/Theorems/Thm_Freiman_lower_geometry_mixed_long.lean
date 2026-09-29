-- Prove2me | Theorems.Thm_Freiman_lower_geometry_mixed_long
-- name    : Freiman.lower_geometry_mixed_long
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:27.728853+00:00
-- url     : https://prove2.me/theorems/2dcf2f27-68fa-439d-a707-a8707a81cf18
-- title:
--   Freiman lower construction: geometry mixed long
-- statement:
--   Actual scalar coverage in the mixed_long source branch, after the exact suffix-target restrictions and actual reached late domain. Any repeated-3 limiting target is retained as its explicit model. Finite certificate obligations must prove nonemptiness, child goodness, both contact directions, all endpoint choices, and anchors.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_section14.tex; lower_120_132.tex; j_family.tex; lower_133_139.tex; lower_140_144.tex; global_selection.tex

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_geometry_mixed_long (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5) : lowerNumericSuccessor t p := by
  sorry
