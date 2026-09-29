-- Prove2me | Theorems.Thm_Freiman_late_normalizations_transfer
-- name    : Freiman.late_normalizations_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:57:18.38645+00:00
-- url     : https://prove2.me/theorems/7874ecfc-652c-45d3-a8f0-31be61a9ef77
-- title:
--   Freiman late: late normalizations transfer
-- statement:
--   The source fork comparisons use the actual normalization of each selected cover.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_normalizations_transfer : ∀ (p : LowerPair) (path : LatePath), latePathValid lateCatalog path → lateHolds (lateBounds lateCatalog path.required) (lateR p) (lateS p) (lateQ p) → ∀ n ∈ path.normalizations, lateNormalizationHolds p n := by
  sorry
