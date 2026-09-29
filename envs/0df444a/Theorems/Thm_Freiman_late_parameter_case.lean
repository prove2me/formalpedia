-- Prove2me | Theorems.Thm_Freiman_late_parameter_case
-- name    : Freiman.late_parameter_case
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:58:49.292993+00:00
-- url     : https://prove2.me/theorems/4f8398b0-2dfa-46a9-b670-e83984913682
-- title:
--   Freiman late: late parameter case
-- statement:
--   The actual normalized continuant ratios lie in the full closed late rectangle [13/17,4/5]×[1/4,4/5], or its right-suffix-3 subrectangle with s≤1/3. This is a finite suffix/continuant fact; hr is the unchanged long-route hypothesis.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_parameter_case (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p)
    (hr : (13/17 : ℝ) ≤ lowerRatio (lowerNormalize p).1) :
    ∃ right3 : Bool, lateMatches p right3 ∧
      certRectangleMem (lateRootRectangle right3) (lateR p) (lateS p) := by
  sorry
