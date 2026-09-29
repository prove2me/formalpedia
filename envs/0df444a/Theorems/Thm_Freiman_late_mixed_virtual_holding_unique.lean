-- Prove2me | Theorems.Thm_Freiman_late_mixed_virtual_holding_unique
-- name    : Freiman.late_mixed_virtual_holding_unique
-- status  : Proved
-- author  : @Koki Yamada
-- created : 2026-09-16T09:31:59.055568+00:00
-- url     : https://prove2.me/theorems/2b7998dc-2266-4021-8259-7adf56ed1e6d
-- title:
--   Freiman late: mixed virtual-upper holding case unique
-- statement:
--   In the mixed-parity virtual-upper case, at most one source case holds at a matching cover. Complementary width tests cannot both hold, so the orientation is unique; the inner equal-parity family of the virtual pair is then unique by the $7/5$ cut versus its complement. Consequently any two holding members of the mixed source list have the same recorded tails.
--
--   $$
--   (z,cs),\ (z',cs')\ \text{hold}\quad\Longrightarrow\quad z=z'.
--   $$
-- source:
--   Freiman report, §15, printed source pages 140–144; uniqueness half of Freiman.late_mixed_virtual_endpoint_from_width_cf.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_mixed_virtual_holding_unique (hw : LowerHistoryWidthLaw) (p : LowerPair) (e : LateEndpoint) (hm : lateMatches p e.right3) (hp : lowerHistoryWordParity (lateContext e.right3) e.words false ≠ lowerHistoryWordParity (lateContext e.right3) e.words true) (hvirt : e.upper = ! lowerHistoryWordParity (lateContext e.right3) e.words (decide (¬ lowerWidth ((lowerNormalize p).2 ++ e.words.2) ≤ lowerWidth ((lowerNormalize p).1 ++ e.words.1)))) (z z' : CertField × CertField) (cs cs' : List CertBound) (h : (z, cs) ∈ lateEndpointCases e.right3 e.words e.upper) (h' : (z', cs') ∈ lateEndpointCases e.right3 e.words e.upper) (hat : lowerHistoryAtBase (lowerNormalize p) cs) (hat' : lowerHistoryAtBase (lowerNormalize p) cs') : z = z' := by
  sorry
