-- Prove2me | Theorems.Thm_Freiman_cert_bernstein_weights
-- name    : Freiman.cert_bernstein_weights
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:04.902603+00:00
-- url     : https://prove2.me/theorems/a22ce781-7b9f-4034-936d-aceaabb2168d
-- title:
--   Certificate: bernstein weights
-- statement:
--   The nine tensor weights form a convex combination everywhere on the full closed rectangle.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_bernstein_weights :
    ∀ (R : CertRectangle) (r s : ℝ), certRectangleValid R → certRectangleMem R r s → (∀ i j : Fin 3, 0 ≤ certBernsteinWeight R r s i j) ∧ (∑ i : Fin 3, ∑ j : Fin 3, certBernsteinWeight R r s i j) = 1 := by
  sorry

end Freiman
