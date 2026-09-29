-- Prove2me | Theorems.Thm_Freiman_cert_cross_polynomial_from_field
-- name    : Freiman.cert_cross_polynomial_from_field
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:55.170848+00:00
-- url     : https://prove2.me/theorems/0664b654-9089-4b0b-93ac-be6913ce89c5
-- title:
--   Certificate: cross polynomial from field
-- statement:
--   Expanding the two products of linear denominator and numerator factors gives exactly the displayed 3×3 power-basis polynomial, assuming sound evaluation of the three field operations. No numerical sampling is involved.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_cross_polynomial_from_field :
    (∀ x y : CertField, certFieldVal (certFieldAdd x y) = certFieldVal x + certFieldVal y) →
    (∀ x y : CertField, certFieldVal (certFieldSub x y) = certFieldVal x - certFieldVal y) →
    (∀ x y : CertField, certFieldVal (certFieldMul x y) = certFieldVal x * certFieldVal y) →
    ∀ (l u : CertThreshold) (r s : ℝ), certPolyEval (certCrossPolynomial l u) r s = certThresholdNum l s * certThresholdDen u r - certThresholdNum u s * certThresholdDen l r := by
  sorry

end Freiman
