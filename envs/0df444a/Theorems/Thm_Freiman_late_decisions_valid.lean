-- Prove2me | Theorems.Thm_Freiman_late_decisions_valid
-- name    : Freiman.late_decisions_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:57:04.887786+00:00
-- url     : https://prove2.me/theorems/726e5916-781a-429d-8205-4b56f2cce2e9
-- title:
--   Freiman late: late decisions valid
-- statement:
--   Collect both complete, closed source decision trees.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_decisions_valid : ∀ right3 : Bool, lateDecisionValid lateCatalog right3 lateRootBounds (lateRootRectangle right3) (lateTree right3) := by
  sorry
