-- Prove2me | Theorems.Thm_Freiman_mobius_determinant_difference_algebra
-- name    : Freiman.mobius_determinant_difference_algebra
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:45.569772+00:00
-- url     : https://prove2.me/theorems/143a1127-ab9f-419e-b72d-3f72263f67ab
-- title:
--   The exact absolute difference of two determinant-one fractional-linear values
-- statement:
--   Subtract two fractional-linear expressions and use the absolute determinant one. All denominator signs are explicit.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.1, found:continuity

import Definitions.Def_Freiman_continuants

namespace Freiman

theorem mobius_determinant_difference_algebra (p pp q qp x y : ℝ) (hq : 0<q) (hqp : 0≤qp) (hx : 0≤x) (hy : 0≤y) (hd : |pp*q-p*qp|=1) :
    |(p+x*pp)/(q+x*qp)-(p+y*pp)/(q+y*qp)| = |x-y|/((q+x*qp)*(q+y*qp)) := by
  sorry

end Freiman
