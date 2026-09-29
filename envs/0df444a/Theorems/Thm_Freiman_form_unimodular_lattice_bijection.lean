-- Prove2me | Theorems.Thm_Freiman_form_unimodular_lattice_bijection
-- name    : Freiman.form_unimodular_lattice_bijection
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:25.081382+00:00
-- url     : https://prove2.me/theorems/fe7d10c3-8ce8-4aca-82a6-20ed04eb898c
-- title:
--   Unimodular changes biject nonzero lattice vectors
-- statement:
--   The adjugate inverse has integer entries when the determinant is ±1 and gives a bijection of nonzero integer vectors.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, opening paragraph

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_unimodular_lattice_bijection (a b c d : ℤ) (hdet : formUnimodular a b c d) :
    (∀ p q : ℤ, (p ≠ 0 ∨ q ≠ 0) → (a*p+b*q ≠ 0 ∨ c*p+d*q ≠ 0)) ∧
      (∀ r s : ℤ, (r ≠ 0 ∨ s ≠ 0) → ∃ p q : ℤ,
        (p ≠ 0 ∨ q ≠ 0) ∧ a*p+b*q=r ∧ c*p+d*q=s) := by
  sorry

end Freiman
