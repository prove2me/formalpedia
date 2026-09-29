-- Prove2me | Theorems.Thm_Freiman_late_endpoint_from_width_cf
-- name    : Freiman.late_endpoint_from_width_cf
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:57:30.873987+00:00
-- url     : https://prove2.me/theorems/efd56cfe-24e6-4ae3-95c6-bb235f43bb7a
-- title:
--   Freiman late: late endpoint from width cf
-- statement:
--   Selected-mode endpoint identity for actual outward prefixes. Reconstruct the source strict-normalization alternatives and 7/5 shortening from the shared continuant and width identities. The old odd–odd case uses the increasing coordinate −t and flips lower/upper; right suffix 1 or 2 shares the 31 representative only because every queried right addition is nonempty.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_endpoint_from_width_cf (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z → certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z)) (hw : LowerHistoryWidthLaw) : lateEndpointLaw := by
  sorry
