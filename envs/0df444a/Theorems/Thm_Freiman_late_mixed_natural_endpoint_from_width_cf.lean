-- Prove2me | Theorems.Thm_Freiman_late_mixed_natural_endpoint_from_width_cf
-- name    : Freiman.late_mixed_natural_endpoint_from_width_cf
-- status  : Proved
-- author  : @Koki Yamada
-- created : 2026-09-16T08:54:48.996058+00:00
-- url     : https://prove2.me/theorems/93e0c578-2b02-457c-bd60-adedf985bb46
-- title:
--   Freiman late: mixed natural-tail selected-mode identity
-- statement:
--   This is the natural-tail case of the mixed-parity late endpoint identity. For a matching cover and a recorded late endpoint whose outward words have opposite length parity, write $w$ for the strictly wider physical side after appending those words, or the left side in a width tie. If the requested endpoint direction is the opposite of the virtual-upper choice of $w$, then every selected mode whose bounds hold reconstructs the actual continued-fraction endpoint from the two natural $3$ or $31$ tails of the original words, together with the unique complementary width orientation. Nonempty right additions make the $31$ representative agree with the physical suffix.
--
--   $$
--   \mathrm{lateActualEndpoint}(p,e)=\mathrm{lateActualValue}(p,e).
--   $$
-- source:
--   Freiman report, §15, printed source pages 140–144; restriction of Freiman.late_mixed_endpoint_from_width_cf to the natural-tail branch of the mixed source list.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_mixed_natural_endpoint_from_width_cf (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z → certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z)) (hw : LowerHistoryWidthLaw) (p : LowerPair) (e : LateEndpoint) (hm : lateMatches p e.right3) (hne1 : e.words.1 ≠ []) (hne2 : e.words.2 ≠ []) (hv : lateEndpointValid lateCatalog e) (hp : lowerHistoryWordParity (lateContext e.right3) e.words false ≠ lowerHistoryWordParity (lateContext e.right3) e.words true) (hnat : e.upper ≠ ! lowerHistoryWordParity (lateContext e.right3) e.words (decide (¬ lowerWidth ((lowerNormalize p).2 ++ e.words.2) ≤ lowerWidth ((lowerNormalize p).1 ++ e.words.1)))) : ∀ ids ∈ e.modes, lateHolds (lateBounds lateCatalog ids) (lateR p) (lateS p) (lateQ p) → lateActualEndpoint p e.words e.upper = lateActualValue p e.value := by
  sorry
