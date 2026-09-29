-- Prove2me | Theorems.Thm_Freiman_late_mixed_virtual_represented
-- name    : Freiman.late_mixed_virtual_represented
-- status  : Proved
-- author  : @Koki Yamada
-- created : 2026-09-16T09:32:02.730469+00:00
-- url     : https://prove2.me/theorems/5bc38cc4-b089-43dd-bd35-b2f010365e00
-- title:
--   Freiman late: mixed virtual-upper source case exists
-- statement:
--   In the mixed-parity virtual-upper case, a matching cover admits a holding source case. Extending the wider physical side by a virtual digit $1$ produces an equal-parity pair; the equal-parity family of that pair, prepended with the unique complementary width orientation, is a member of the mixed source list whose certificate bounds hold at the normalized cover, and whose recorded tails reconstruct the actual continued-fraction endpoint.
--
--   $$
--   \exists\, z,\,cs:\quad (z,cs)\in\mathrm{lateEndpointCases}(e)\ \wedge\ \mathrm{bounds\ hold}(cs)\ \wedge\ \mathrm{lateActualEndpoint}(p,e)=\mathrm{lateActualValue}(p,z).
--   $$
-- source:
--   Freiman report, §15, printed source pages 140–144; existence half of Freiman.late_mixed_virtual_endpoint_from_width_cf.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_mixed_virtual_represented (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z → certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z)) (hw : LowerHistoryWidthLaw) (p : LowerPair) (e : LateEndpoint) (hm : lateMatches p e.right3) (hne1 : e.words.1 ≠ []) (hne2 : e.words.2 ≠ []) (hp : lowerHistoryWordParity (lateContext e.right3) e.words false ≠ lowerHistoryWordParity (lateContext e.right3) e.words true) (hvirt : e.upper = ! lowerHistoryWordParity (lateContext e.right3) e.words (decide (¬ lowerWidth ((lowerNormalize p).2 ++ e.words.2) ≤ lowerWidth ((lowerNormalize p).1 ++ e.words.1)))) : ∃ z cs, (z, cs) ∈ lateEndpointCases e.right3 e.words e.upper ∧ lowerHistoryAtBase (lowerNormalize p) cs ∧ lateActualEndpoint p e.words e.upper = lateActualValue p z := by
  sorry
