-- Prove2me | Theorems.Thm_Freiman_cert_field_sub
-- name    : Freiman.cert_field_sub
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:45.479158+00:00
-- url     : https://prove2.me/theorems/d9262411-df94-44c9-b4a4-6726237333c0
-- title:
--   Certificate: field sub
-- statement:
--   Evaluation in ℝ respects the exact four-rational sub operation; the stored field representation has its specified algebraic meaning.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_field_sub :
    ∀ x y : CertField, certFieldVal (certFieldSub x y) = certFieldVal x - certFieldVal y := by
  sorry

end Freiman
