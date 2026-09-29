-- Prove2me | Theorems.Thm_Freiman_cert_diagonal_order_from_factors
-- name    : Freiman.cert_diagonal_order_from_factors
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:27:12.195503+00:00
-- url     : https://prove2.me/theorems/9acd19fc-6a40-402b-9ed4-3222b64513f8
-- title:
--   Freiman M2B certificate: cert diagonal order from factors
-- statement:
--   The sign of r−s agrees with the selected closed half-rectangle; multiply the signed bilinear bound and divide by the two positive threshold denominators. Equality r=s is retained.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; m2b_readable_model.json, SHA256 a5ac6d3c8e0148e2e3137e8cfa09a2715de6a993dd6ab01eda4842a96bba4cdf.

import Definitions.Def_Freiman_certDiagonal

open Freiman

theorem Freiman.cert_diagonal_order_from_factors :
    (∀ (a b c : CertField) (r s : ℝ), certPolyEval (certDiagonalPolynomial a b c) r s = (r-s)*certDiagonalFactor a b c r s) → (∀ (w : CertDiagonalData), certDiagonalDataValid w → (∀ i j : Fin 2, 0 ≤ certFieldVal (w.corners i j)) → ∀ r s : ℝ, certRectangleMem w.rectangle r s → 0 ≤ (if w.positiveDirection then (1:ℝ) else -1)*certDiagonalFactor w.a w.b w.c r s) → (∀ (w : CertDiagonalData), certDiagonalDataValid w → ∀ i j : Fin 2, 0 ≤ certFieldVal (w.corners i j)) → (∀ z : CertField, (certFieldLower z:ℝ) ≤ certFieldVal z) → (∀ (l u : CertThreshold) (r s : ℝ), certPolyEval (certCrossPolynomial l u) r s = certThresholdNum l s * certThresholdDen u r - certThresholdNum u s * certThresholdDen l r) → (∀ (l u : CertThreshold) (r s : ℝ), 0 < certThresholdDen l r → 0 < certThresholdDen u r → (0 ≤ certThresholdNum l s*certThresholdDen u r-certThresholdNum u s*certThresholdDen l r ↔ certThresholdVal u r s ≤ certThresholdVal l r s) ∧ (0 < certThresholdNum l s*certThresholdDen u r-certThresholdNum u s*certThresholdDen l r ↔ certThresholdVal u r s < certThresholdVal l r s)) → (∀ (t : CertThreshold) (r : ℝ), 0 ≤ r → 0 ≤ certFieldVal t.x0 → 0 ≤ certFieldVal t.x1 → 0 < certThresholdDen t r) → ∀ (w : CertDiagonalData), certDiagonalDataValid w → ∀ r s : ℝ, certRectangleMem w.rectangle r s → certDiagonalSide w r s → certThresholdVal w.upperThreshold r s ≤ certThresholdVal w.lowerThreshold r s := by
  sorry
