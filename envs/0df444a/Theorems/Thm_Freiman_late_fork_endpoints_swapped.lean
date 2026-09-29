-- Prove2me | Theorems.Thm_Freiman_late_fork_endpoints_swapped
-- name    : Freiman.late_fork_endpoints_swapped
-- status  : Open
-- author  : @Koki Yamada
-- created : 2026-09-16T10:54:43.311338+00:00
-- url     : https://prove2.me/theorems/d340d40e-9a5c-40a1-a32e-72749ef92e02
-- title:
--   Freiman late: swapped fork endpoint alignment
-- statement:
--   This is the swapped case of incoming-order fork alignment. For a matching cover and a catalogue path whose recorded fork orientation is right-wide, `lowerChild` swaps the pair before appending the goodness digit $d\in\{1,2\}$, while the source fork record retains physical order. The two pairs are swaps of each other; their continued-fraction endpoints nevertheless agree, including at a possible width tie after the digit is appended.
--
--   $$
--   \mathrm{lowerEndpoint}(\mathrm{child}(\mathrm{child}(p,n),d))=\mathrm{lowerEndpoint}(N\mathbin{++}\mathrm{forkWords}(n,d)).
--   $$
-- source:
--   Freiman report, §15, printed source pages 140–144; swapped case of Freiman.late_fork_endpoints.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_fork_endpoints_swapped (p : LowerPair) (path : LatePath) (hm : lateMatches p path.right3) (hv : latePathValid lateCatalog path) (hn : ∀ n ∈ path.normalizations, lateNormalizationHolds p n) (n : LateNormalization) (hmem : n ∈ path.normalizations) (d : ℕ+) (hd : d ∈ ([1, 2] : List ℕ+)) (upper : Bool) (hw : n.wide = true) : lowerEndpoint (lowerChild (lowerChild p n.label) ([d], [])) upper = lowerEndpoint (lowerHistoryAppend (lowerNormalize p) (lateForkWords n d)) upper := by
  sorry
