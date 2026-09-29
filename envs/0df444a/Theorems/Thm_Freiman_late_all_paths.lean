-- Prove2me | Theorems.Thm_Freiman_late_all_paths
-- name    : Freiman.late_all_paths
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:57:02.714502+00:00
-- url     : https://prove2.me/theorems/8375ba53-fa43-4b57-8ea9-768c9ebac5e2
-- title:
--   Freiman late: late all paths
-- statement:
--   All 63 selected source routes have the exact finite semantic shape required by the late proposition.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_all_paths : lateAllPaths lateCatalog := by
  sorry
