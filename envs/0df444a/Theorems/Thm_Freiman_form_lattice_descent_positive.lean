-- Prove2me | Theorems.Thm_Freiman_form_lattice_descent_positive
-- name    : Freiman.form_lattice_descent_positive
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:01.06389+00:00
-- url     : https://prove2.me/theorems/75f9d176-e0be-4b86-b608-1ddc394e5289
-- title:
--   Positive-second-coordinate descent
-- statement:
--   The strict sub-infimum assumption forces a_n q≤p≤(a_n+1)q. Replace (n,p,q) by (n+1,q,p−a_nq); the absolute form value is unchanged and |p|+|q| strictly decreases.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, positive-q case in found:form-minimum

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_lattice_descent_positive (R : ReducedOrbit) (n p q : ℤ) (hp : 0 < p) (hq : 0 < q) (hv : |reducedValue (R.alpha n) (R.beta n) p q| < orbitReciprocalInfimum R) :
    let r := p - ((R.digits n : ℕ) : ℤ)*q;
      (q ≠ 0 ∨ r ≠ 0) ∧
      |reducedValue (R.alpha (n+1)) (R.beta (n+1)) q r| = |reducedValue (R.alpha n) (R.beta n) p q| ∧
      latticeSize q r < latticeSize p q := by
  sorry

end Freiman
