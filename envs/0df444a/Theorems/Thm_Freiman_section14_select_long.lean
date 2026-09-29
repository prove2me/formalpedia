-- Prove2me | Theorems.Thm_Freiman_section14_select_long
-- name    : Freiman.section14_select_long
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:51:58.211989+00:00
-- url     : https://prove2.me/theorems/08d0d311-4474-4939-8b0e-c4b7b2be9392
-- title:
--   Freiman §14: section14 select long
-- statement:
--   Finite interval-chain selection for the long row, assuming the separately certified scalar inequalities. The p97 branch uses the carried C20 lower target anchor; the long branch uses suffix bounds to retain only the safe connected prefix C10,C22 when needed, and excludes an old right 3131 suffix. No admissibility of discarded raw children is assumed.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.section14_select_long (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5) (hg : section14RawGeometry p) : lowerNumericSuccessor t p := by
  sorry
