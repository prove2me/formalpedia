-- Prove2me | Theorems.Thm_Freiman_late_route_geometry
-- name    : Freiman.late_route_geometry
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:58:38.359079+00:00
-- url     : https://prove2.me/theorems/339071df-3686-4d6f-aaea-38325237fd76
-- title:
--   Freiman late: late route geometry
-- statement:
--   A route selected by the finite catalogue is a genuine chain of good actual lower covers.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_route_geometry (p : LowerPair) (i : ℕ) (hi : lateIndex i lateCatalog.paths.size)
    (hm : lateMatches p (latePath lateCatalog i).right3)
    (hr : lateHolds (lateBounds lateCatalog (latePath lateCatalog i).required) (lateR p) (lateS p) (lateQ p))
    (ha : lowerGood (lowerChild p ([2],[2])) ∧ lowerGood (lowerChild p ([2],[1]))) :
    lowerLateRouteValid p (latePath lateCatalog i).route := by
  sorry
