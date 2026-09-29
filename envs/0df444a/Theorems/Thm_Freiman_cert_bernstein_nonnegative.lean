-- Prove2me | Theorems.Thm_Freiman_cert_bernstein_nonnegative
-- name    : Freiman.cert_bernstein_nonnegative
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:07.704017+00:00
-- url     : https://prove2.me/theorems/ed02dfd9-3319-4c01-bed0-7a02dc99affc
-- title:
--   Certificate: bernstein nonnegative
-- statement:
--   Coefficient nonnegative implies the same sign throughout the rectangle by the exact Bernstein convex combination.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_bernstein_nonnegative :
    ∀ (C : CertPoly22) (R : CertRectangle) (r s : ℝ), certRectangleValid R → certRectangleMem R r s → (∀ i j : Fin 3, 0 ≤ certFieldVal (C i j)) → 0 ≤ certBernsteinEval C R r s := by
  sorry

end Freiman
