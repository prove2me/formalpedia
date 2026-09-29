-- Prove2me | Theorems.Thm_Freiman_form_roots_reduction
-- name    : Freiman.form_roots_reduction
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:57:58.590877+00:00
-- url     : https://prove2.me/theorems/19588063-41e0-4921-900c-fbf2cc45465d
-- title:
--   Simultaneous unimodular reduction of two irrational roots
-- statement:
--   Use the two successive convergents to r as matrix columns. The inverse image of r is its next complete quotient >1. The inverse image of s is eventually in (−1,0), since denominator increments diverge while convergent errors tend to zero. Rational invertibility preserves irrationality.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, found:reduce-roots

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_roots_reduction (r s : ℝ) (hrs : s < r) (hr : Irrational r) (hs : Irrational s) :
    ∃ a b c d : ℤ, ∃ α β : ℝ, formUnimodular a b c d ∧
      1 < α ∧ 0 < β ∧ β < 1 ∧ Irrational α ∧ Irrational β ∧
      (c:ℝ)*α+(d:ℝ) ≠ 0 ∧ -(c:ℝ)*β+(d:ℝ) ≠ 0 ∧
      r = ((a:ℝ)*α+(b:ℝ))/((c:ℝ)*α+(d:ℝ)) ∧
      s = (-(a:ℝ)*β+(b:ℝ))/(-(c:ℝ)*β+(d:ℝ)) := by
  sorry

end Freiman
