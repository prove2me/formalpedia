-- Prove2me | Theorems.Thm_Freiman_late_route_from_checks
-- name    : Freiman.late_route_from_checks
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:57:34.590819+00:00
-- url     : https://prove2.me/theorems/6e7b9174-98a3-46dc-b059-f45744135022
-- title:
--   Freiman late: late route from checks
-- statement:
--   Finite closed-interval gluing for one validated path: nonemptiness plus two strict cross-inequalities makes each intermediate cover good, both weak cross-inequalities make adjacent covers meet, and the two externally supplied anchor-goodness facts complete the unchanged route predicate. This is the report’s route topology, without any finite scalar search.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_route_from_checks (ho : ∀ p : LowerPair, lowerEndpoint p false ≤ lowerEndpoint p true) (p : LowerPair) (path : LatePath) (hm : ¬ lowerMixed p)
    (hv : latePathValid lateCatalog path)
    (ha : lowerGood (lowerChild p ([2],[2])) ∧ lowerGood (lowerChild p ([2],[1])))
    (hn : ∀ n ∈ path.normalizations, lateNormalizationHolds p n)
    (hf : lateForkAlignment p path)
    (hc : ∀ c ∈ path.checks, lateSpecHolds p (lateCheckSpec lateCatalog c)) :
    lowerLateRouteValid p path.route := by
  sorry
