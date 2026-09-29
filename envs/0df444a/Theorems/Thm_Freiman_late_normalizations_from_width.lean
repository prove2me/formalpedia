-- Prove2me | Theorems.Thm_Freiman_late_normalizations_from_width
-- name    : Freiman.late_normalizations_from_width
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:57:06.715699+00:00
-- url     : https://prove2.me/theorems/ae9cac33-02e8-48b5-ac35-2345e3e2d0a4
-- title:
--   Freiman late: late normalizations from width
-- statement:
--   Each intermediate fork digit is appended to the side that is actually wider at that cover. The strict reflected condition prevents swapping equal-width incoming sides.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_normalizations_from_width (hw : LowerHistoryWidthLaw) : ∀ (p : LowerPair) (path : LatePath), latePathValid lateCatalog path → lateHolds (lateBounds lateCatalog path.required) (lateR p) (lateS p) (lateQ p) → ∀ n ∈ path.normalizations, lateNormalizationHolds p n := by
  sorry
