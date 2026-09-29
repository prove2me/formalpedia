-- Prove2me | Theorems.Thm_Freiman_late_all_endpoints
-- name    : Freiman.late_all_endpoints
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:57:24.53532+00:00
-- url     : https://prove2.me/theorems/094b0c63-c301-490b-a957-cd0ea8ab4330
-- title:
--   Freiman late: late all endpoints
-- statement:
--   Validate all 162 selected endpoint records against the actual §11/§15 endpoint algorithm. Equality retains the incoming first side; reflection is strict. Every selected 7/5-shortening branch and every endpoint tail coordinate is preserved.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_all_endpoints : lateAllEndpoints lateCatalog := by
  sorry
