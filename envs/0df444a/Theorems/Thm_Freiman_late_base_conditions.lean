-- Prove2me | Theorems.Thm_Freiman_late_base_conditions
-- name    : Freiman.late_base_conditions
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:58:34.877685+00:00
-- url     : https://prove2.me/theorems/2c66fe3a-f63c-4b6f-a4a7-116f7b0bcdd1
-- title:
--   Freiman late: late base conditions
-- statement:
--   The reached late domain supplies exactly the three source tree premises.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_base_conditions (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p) : lateHolds lateRootBounds (lateR p) (lateS p) (lateQ p) := by
  sorry
