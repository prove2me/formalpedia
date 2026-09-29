-- Prove2me | Theorems.Thm_Freiman_cert_threshold_cross_order
-- name    : Freiman.cert_threshold_cross_order
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:22.252532+00:00
-- url     : https://prove2.me/theorems/7563e0e1-addc-4d21-9901-1b21ca98f92a
-- title:
--   Certificate: threshold cross order
-- statement:
--   With positive denominators, the weak or strict sign of the cleared polynomial is equivalent to the corresponding order of the two threshold rational functions.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_threshold_cross_order :
    ∀ (l u : CertThreshold) (r s : ℝ), 0 < certThresholdDen l r → 0 < certThresholdDen u r →
    (0 ≤ certThresholdNum l s*certThresholdDen u r-certThresholdNum u s*certThresholdDen l r ↔ certThresholdVal u r s ≤ certThresholdVal l r s) ∧
    (0 < certThresholdNum l s*certThresholdDen u r-certThresholdNum u s*certThresholdDen l r ↔ certThresholdVal u r s < certThresholdVal l r s) := by
  sorry

end Freiman
