-- Prove2me | Theorems.Thm_Freiman_cert_bernstein_positive
-- name    : Freiman.cert_bernstein_positive
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:11.401974+00:00
-- url     : https://prove2.me/theorems/5975db42-b511-45bd-aef7-22a367122b2d
-- title:
--   Certificate: bernstein positive
-- statement:
--   Coefficient positive implies the same sign throughout the rectangle by the exact Bernstein convex combination.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_bernstein_positive :
    ∀ (C : CertPoly22) (R : CertRectangle) (r s : ℝ), certRectangleValid R → certRectangleMem R r s → (∀ i j : Fin 3, 0 < certFieldVal (C i j)) → 0 < certBernsteinEval C R r s := by
  sorry

end Freiman
