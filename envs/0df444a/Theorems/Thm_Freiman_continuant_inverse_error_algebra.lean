-- Prove2me | Theorems.Thm_Freiman_continuant_inverse_error_algebra
-- name    : Freiman.continuant_inverse_error_algebra
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:20.287383+00:00
-- url     : https://prove2.me/theorems/f2b94fba-2dcc-47d5-b008-de0c54e83461
-- title:
--   Determinant-one Möbius inverse-error algebra
-- statement:
--   Subtract p/q from the Möbius expression, use the absolute determinant one, and invert the positive error denominator. This is the purely rational algebra in the report’s exact Perron identity.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, first displayed identity of found:perron

import Definitions.Def_Freiman_continuants

namespace Freiman

theorem continuant_inverse_error_algebra (p pp q qp τ x : ℝ) (hq : 0 < q) (hqp : 0 ≤ qp) (hτ : 0 < τ) (hx : x=(p+τ*pp)/(q+τ*qp)) (hdet : |pp*q-p*qp|=1) :
    1 / (q * |q*x-p|) = 1/τ + qp/q := by
  sorry

end Freiman
