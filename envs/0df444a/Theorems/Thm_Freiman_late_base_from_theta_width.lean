-- Prove2me | Theorems.Thm_Freiman_late_base_from_theta_width
-- name    : Freiman.late_base_from_theta_width
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:58:18.200671+00:00
-- url     : https://prove2.me/theorems/d38cf7fd-827e-44ed-8e36-9af2864146a4
-- title:
--   Freiman late: late base from theta width
-- statement:
--   Identify the three literal root bounds B17/B52/B258 with full-width normalization, H7≥31/100 and the weak consequence of not A9. Denominator positivity and all exact tail coordinates are retained; no additional goodness is silently assumed.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_base_from_theta_width (ht : ∀ i ∈ ([3,20,22,25,28,35,36,63,65,66,68,70,90,94] : List ℕ), certFieldVal (lowerHistoryTheta i) = lowerTheta i) (hw : LowerHistoryWidthLaw) (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p) :
    lateHolds lateRootBounds (lateR p) (lateS p) (lateQ p) := by
  sorry
