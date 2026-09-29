-- Prove2me | Theorems.Thm_Freiman_lower_geometry_equal_small_left
-- name    : Freiman.lower_geometry_equal_small_left
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:30.970032+00:00
-- url     : https://prove2.me/theorems/bb6b4501-6f9a-4f4d-bbcd-c6e62d7d826b
-- title:
--   Freiman lower construction: geometry equal small left
-- statement:
--   Actual scalar coverage in the equal_small_left source branch, after the exact suffix-target restrictions and actual reached late domain. Any repeated-3 limiting target is retained as its explicit model. Finite certificate obligations must prove nonemptiness, child goodness, both contact directions, all endpoint choices, and anchors.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_section14.tex; lower_120_132.tex; j_family.tex; lower_133_139.tex; lower_140_144.tex; global_selection.tex

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_geometry_equal_small_left (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ lowerA p 9 ∧ lowerL p) : lowerNumericSuccessor t p := by
  sorry
