-- Prove2me | Theorems.Thm_Freiman_late_fork_endpoints_unswapped
-- name    : Freiman.late_fork_endpoints_unswapped
-- status  : Proved
-- author  : @Koki Yamada
-- created : 2026-09-16T10:55:01.242408+00:00
-- url     : https://prove2.me/theorems/e0f06e7a-6c0d-4e54-b18a-6abbfdeb24af
-- title:
--   Freiman late: unswapped fork endpoint alignment
-- statement:
--   This is the unswapped case of incoming-order fork alignment. For a matching cover and a catalogue path whose recorded fork orientation is left-wide, appending a goodness digit $d\in\{1,2\}$ to the normalized child is the same pair as appending the source fork words to the normalized cover. Consequently the two pairs have the same continued-fraction endpoints.
--
--   $$
--   \mathrm{lowerEndpoint}(\mathrm{child}(\mathrm{child}(p,n),d))=\mathrm{lowerEndpoint}(N\mathbin{++}\mathrm{forkWords}(n,d)).
--   $$
-- source:
--   Freiman report, §15, printed source pages 140–144; unswapped case of Freiman.late_fork_endpoints.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_fork_endpoints_unswapped (p : LowerPair) (path : LatePath) (hm : lateMatches p path.right3) (hv : latePathValid lateCatalog path) (hn : ∀ n ∈ path.normalizations, lateNormalizationHolds p n) (n : LateNormalization) (hmem : n ∈ path.normalizations) (d : ℕ+) (hd : d ∈ ([1, 2] : List ℕ+)) (upper : Bool) (hw : n.wide = false) : lowerEndpoint (lowerChild (lowerChild p n.label) ([d], [])) upper = lowerEndpoint (lowerHistoryAppend (lowerNormalize p) (lateForkWords n d)) upper := by
  sorry
