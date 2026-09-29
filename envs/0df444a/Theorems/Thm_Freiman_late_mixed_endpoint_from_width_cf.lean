-- Prove2me | Theorems.Thm_Freiman_late_mixed_endpoint_from_width_cf
-- name    : Freiman.late_mixed_endpoint_from_width_cf
-- status  : Proved
-- author  : @Koki Yamada
-- created : 2026-09-16T01:17:21.291567+00:00
-- url     : https://prove2.me/theorems/300111e6-fcea-4d1a-8b02-39094aae1ae9
-- title:
--   Freiman late: mixed-parity selected-mode endpoint identity
-- statement:
--   This is the mixed word-parity case of the selected-mode late endpoint identity. For a matching cover and a recorded late endpoint whose two outward words have opposite length parity, every selected mode whose certificate bounds hold reconstructs the actual continued-fraction endpoint. The mixed rule either extends the wider side by a virtual digit $1$ and reduces to an equal-parity case, or uses the two natural tails when the requested endpoint is the opposite virtual-upper choice. Strict complementary width tests remain unique. Nonempty right additions make the $31$ representative agree with the physical suffix, and the odd-left coordinate $-t$ exchanges lower and upper endpoints.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees. Restriction of Freiman.late_endpoint_from_width_cf to mixed word-parity endpoints.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_mixed_endpoint_from_width_cf (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z → certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z)) (hw : LowerHistoryWidthLaw) (p : LowerPair) (e : LateEndpoint) (hm : lateMatches p e.right3) (hne1 : e.words.1 ≠ []) (hne2 : e.words.2 ≠ []) (hv : lateEndpointValid lateCatalog e) (hp : lowerHistoryWordParity (lateContext e.right3) e.words false ≠ lowerHistoryWordParity (lateContext e.right3) e.words true) : ∀ ids ∈ e.modes, lateHolds (lateBounds lateCatalog ids) (lateR p) (lateS p) (lateQ p) → lateActualEndpoint p e.words e.upper = lateActualValue p e.value := by
  sorry
