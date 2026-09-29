-- Prove2me | Theorems.Thm_Freiman_late_equal_endpoint_from_width_cf
-- name    : Freiman.late_equal_endpoint_from_width_cf
-- status  : Proved
-- author  : @Koki Yamada
-- created : 2026-09-16T01:17:42.156836+00:00
-- url     : https://prove2.me/theorems/878e0ea2-4544-4e0c-b735-f4377ad5d1cd
-- title:
--   Freiman late: equal-parity selected-mode endpoint identity
-- statement:
--   This is the equal word-parity case of the selected-mode late endpoint identity. For a matching cover and a recorded late endpoint whose two outward words have the same length parity in the source context, every selected mode whose certificate bounds hold at the normalized ratios reconstructs the actual continued-fraction endpoint of those words from the recorded tails. The two sides of a matching cover already have equal length parity, so the appended pair is equal-parity exactly when the words are. Strict complementary width tests and the $7/5$ shortening cut select a unique source case; nonempty right additions make the $31$ representative of a last digit $1$ or $2$ agree with the physical suffix. The odd-left increasing coordinate $-t$ exchanges lower and upper endpoints.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees. Restriction of Freiman.late_endpoint_from_width_cf to equal word-parity endpoints.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_equal_endpoint_from_width_cf (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z → certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z)) (hw : LowerHistoryWidthLaw) (p : LowerPair) (e : LateEndpoint) (hm : lateMatches p e.right3) (hne1 : e.words.1 ≠ []) (hne2 : e.words.2 ≠ []) (hv : lateEndpointValid lateCatalog e) (hp : lowerHistoryWordParity (lateContext e.right3) e.words false = lowerHistoryWordParity (lateContext e.right3) e.words true) : ∀ ids ∈ e.modes, lateHolds (lateBounds lateCatalog ids) (lateR p) (lateS p) (lateQ p) → lateActualEndpoint p e.words e.upper = lateActualValue p e.value := by
  sorry
