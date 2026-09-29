-- Prove2me | Theorems.Thm_Freiman_cert_diagonal_threshold_order
-- name    : Freiman.cert_diagonal_threshold_order
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:27:18.077977+00:00
-- url     : https://prove2.me/theorems/1a9d6c0f-0fef-450f-a025-9014ac67ad17
-- title:
--   Freiman M2B certificate: cert diagonal threshold order
-- statement:
--   The report’s diagonal factorization yields the weak threshold order on its selected half-rectangle. Strict q premises handle the common diagonal.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; m2b_readable_model.json, SHA256 a5ac6d3c8e0148e2e3137e8cfa09a2715de6a993dd6ab01eda4842a96bba4cdf.

import Definitions.Def_Freiman_certDiagonal

open Freiman

theorem Freiman.cert_diagonal_threshold_order :
    ∀ (w : CertDiagonalData), certDiagonalDataValid w → ∀ r s : ℝ, certRectangleMem w.rectangle r s → certDiagonalSide w r s → certThresholdVal w.upperThreshold r s ≤ certThresholdVal w.lowerThreshold r s := by
  sorry
