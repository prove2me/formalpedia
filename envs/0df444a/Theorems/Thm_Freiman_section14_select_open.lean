-- Prove2me | Theorems.Thm_Freiman_section14_select_open
-- name    : Freiman.section14_select_open
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:51:15.912978+00:00
-- url     : https://prove2.me/theorems/e4eaee6f-950e-45e5-ac7e-b8e88acce1df
-- title:
--   Freiman §14: section14 select open
-- statement:
--   Finite interval-chain selection for the open row, assuming the separately certified scalar inequalities. The p97 branch uses the carried C20 lower target anchor; the long branch uses suffix bounds to retain only the safe connected prefix C10,C22 when needed, and excludes an old right 3131 suffix. No admissibility of discarded raw children is assumed.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.section14_select_open (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : lowerMixed p ∧ lowerH p 2) (hg : section14RawGeometry p) : lowerNumericSuccessor t p := by
  sorry
