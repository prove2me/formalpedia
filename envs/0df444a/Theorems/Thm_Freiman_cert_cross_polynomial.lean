-- Prove2me | Theorems.Thm_Freiman_cert_cross_polynomial
-- name    : Freiman.cert_cross_polynomial
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:50.09303+00:00
-- url     : https://prove2.me/theorems/f9ff9db0-f5f6-4e19-a2c2-e75b95517e44
-- title:
--   Certificate: cross polynomial
-- statement:
--   The stored polynomial evaluates to the numerator obtained by subtracting the two threshold rational functions after multiplication by their denominators.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_cross_polynomial :
    ∀ (l u : CertThreshold) (r s : ℝ), certPolyEval (certCrossPolynomial l u) r s = certThresholdNum l s * certThresholdDen u r - certThresholdNum u s * certThresholdDen l r := by
  sorry

end Freiman
