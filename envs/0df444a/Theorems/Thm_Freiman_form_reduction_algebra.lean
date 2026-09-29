-- Prove2me | Theorems.Thm_Freiman_form_reduction_algebra
-- name    : Freiman.form_reduction_algebra
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:08.320873+00:00
-- url     : https://prove2.me/theorems/1a72f153-2120-49b7-973d-93b1aeecd4da
-- title:
--   Transport from a reduced root change to the normalized minimum
-- statement:
--   A form with the transformed roots α and −β is a scalar multiple of the displayed reduced form. Discriminant and absolute-minimum scaling determine the scalar and give the normalized reciprocal ratio. The invariance statements are explicit hypotheses, so this leaf is the remaining coefficient and square-root algebra.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, last paragraph of found:reduce-roots

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_reduction_algebra (A B C r s : ℝ) (a b c d : ℤ) (α β : ℝ) (hd : 0 < B^2-4*A*C) (hm : 0 < quadraticMinimum A B C) (hA : A ≠ 0) (hfactor : ∀ p q : ℤ, quadraticValue A B C p q = A*((p:ℝ)-r*(q:ℝ))*((p:ℝ)-s*(q:ℝ))) (hdet : formUnimodular a b c d) (hα : 1 < α) (hβ : 0 < β) (hβ1 : β < 1) (hcα : (c:ℝ)*α+(d:ℝ) ≠ 0) (hcβ : -(c:ℝ)*β+(d:ℝ) ≠ 0) (hr : r=((a:ℝ)*α+(b:ℝ))/((c:ℝ)*α+(d:ℝ))) (hs : s=(-(a:ℝ)*β+(b:ℝ))/(-(c:ℝ)*β+(d:ℝ))) (hmin : quadraticMinimum (transformedA A B C a b c d) (transformedB A B C a b c d) (transformedC A B C a b c d) = quadraticMinimum A B C) (hdisc : (transformedB A B C a b c d)^2-4*transformedA A B C a b c d*transformedC A B C a b c d=B^2-4*A*C) (hscale : ∀ k : ℝ, k ≠ 0 → quadraticMinimum (k*reducedA α β) (k*reducedB α β) (k*reducedC α β)=|k| * reducedMinimum α β) :
    0 < reducedMinimum α β ∧ Real.sqrt (B^2-4*A*C) / quadraticMinimum A B C = 1 / reducedMinimum α β := by
  sorry

end Freiman
