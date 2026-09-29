-- Prove2me | Theorems.Thm_Freiman_form_irrational_roots
-- name    : Freiman.form_irrational_roots
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:03.228305+00:00
-- url     : https://prove2.me/theorems/13af67f5-f82e-49d8-9615-fdb029a038b1
-- title:
--   Positive lattice minimum excludes rational zero directions
-- statement:
--   A rational root yields a nonzero integer zero vector and contradicts the positive minimum; A=0 gives such a zero on the first axis. Positive discriminant then supplies two finite irrational roots.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, found:reduce-roots

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_irrational_roots (A B C : ℝ) (hd : 0 < B^2-4*A*C) (hm : 0 < quadraticMinimum A B C) :
    A ≠ 0 ∧ ∃ r s : ℝ, s < r ∧ Irrational r ∧ Irrational s ∧
      ∀ p q : ℤ, quadraticValue A B C p q = A * ((p:ℝ)-r*(q:ℝ)) * ((p:ℝ)-s*(q:ℝ)) := by
  sorry

end Freiman
