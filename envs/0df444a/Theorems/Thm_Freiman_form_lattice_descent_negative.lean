-- Prove2me | Theorems.Thm_Freiman_form_lattice_descent_negative
-- name    : Freiman.form_lattice_descent_negative
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:03.65456+00:00
-- url     : https://prove2.me/theorems/a5dcce09-f72d-4a4a-98a1-e344a92280a0
-- title:
--   Negative-second-coordinate descent
-- statement:
--   Writing q=−Q, the other-axis bound forces a_(n−1)p≤Q≤(a_(n−1)+1)p. Replace (n,p,−Q) by (n−1,a_(n−1)p−Q,p), preserving the absolute value and strictly decreasing the integer coordinate norm.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, negative-q case in found:form-minimum

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_lattice_descent_negative (R : ReducedOrbit) (n p q : ℤ) (hp : 0 < p) (hq : q < 0) (hv : |reducedValue (R.alpha n) (R.beta n) p q| < orbitReciprocalInfimum R) :
    let r := ((R.digits (n-1) : ℕ) : ℤ)*p+q;
      (r ≠ 0 ∨ p ≠ 0) ∧
      |reducedValue (R.alpha (n-1)) (R.beta (n-1)) r p| = |reducedValue (R.alpha n) (R.beta n) p q| ∧
      latticeSize r p < latticeSize p q := by
  sorry

end Freiman
