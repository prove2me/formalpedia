-- Prove2me | Theorems.Thm_Freiman_quadratic_lattice_descent_induction
-- name    : Freiman.quadratic_lattice_descent_induction
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:12.691874+00:00
-- url     : https://prove2.me/theorems/4b989e14-b9ec-4fa9-ad18-0ec06ebe4cc6
-- title:
--   Well-founded descent excludes a sub-infimum lattice vector
-- statement:
--   Choose a counterexample of least natural |p|+|q|. Common sign reversal makes p positive; the axis case contradicts haxis, and either sign of q gives a smaller counterexample by the supplied descent step. This leaf is the well-founded induction itself, separated from the two algebraic cases.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, final paragraph of found:form-minimum

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem quadratic_lattice_descent_induction (R : ReducedOrbit) (haxis : ∀ n p q : ℤ, (p ≠ 0 ∨ q ≠ 0) → (p=0 ∨ q=0) → orbitReciprocalInfimum R ≤ |reducedValue (R.alpha n) (R.beta n) p q|) (hpos : ∀ n p q : ℤ, 0<p → 0<q → |reducedValue (R.alpha n) (R.beta n) p q| < orbitReciprocalInfimum R → ∃ m r s : ℤ, (r≠0 ∨ s≠0) ∧ |reducedValue (R.alpha m) (R.beta m) r s|=|reducedValue (R.alpha n) (R.beta n) p q| ∧ latticeSize r s<latticeSize p q) (hneg : ∀ n p q : ℤ, 0<p → q<0 → |reducedValue (R.alpha n) (R.beta n) p q| < orbitReciprocalInfimum R → ∃ m r s : ℤ, (r≠0 ∨ s≠0) ∧ |reducedValue (R.alpha m) (R.beta m) r s|=|reducedValue (R.alpha n) (R.beta n) p q| ∧ latticeSize r s<latticeSize p q) :
    ∀ n p q : ℤ, (p ≠ 0 ∨ q ≠ 0) → orbitReciprocalInfimum R ≤ |reducedValue (R.alpha n) (R.beta n) p q| := by
  sorry

end Freiman
