-- Prove2me | Theorems.Thm_Freiman_late_fork_endpoints
-- name    : Freiman.late_fork_endpoints
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:57:37.142976+00:00
-- url     : https://prove2.me/theorems/865c4263-d203-48d7-a436-f49736acb4e2
-- title:
--   Freiman late: late fork endpoints
-- statement:
--   Actual incoming-order alignment of every source goodness fork. When the right side was wider, lowerChild swaps the pair before appending, while the source endpoint record retains physical order. This lemma must justify the resulting endpoint equality, including any child width tie; no unconditional swap identity is assumed.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_fork_endpoints (p : LowerPair) (path : LatePath) (hm : lateMatches p path.right3) (hv : latePathValid lateCatalog path) (hn : ∀ n ∈ path.normalizations, lateNormalizationHolds p n) : lateForkAlignment p path := by
  sorry
