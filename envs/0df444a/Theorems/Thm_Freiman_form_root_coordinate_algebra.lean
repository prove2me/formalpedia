-- Prove2me | Theorems.Thm_Freiman_form_root_coordinate_algebra
-- name    : Freiman.form_root_coordinate_algebra
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:48.067174+00:00
-- url     : https://prove2.me/theorems/bb1ed2cf-8bd5-4902-a22b-ba00d66eac38
-- title:
--   Reconstruct the reduced roots from a convergent matrix
-- statement:
--   Use G_n as the integer matrix, α as its next complete quotient and β as minus the second inverse root. The domain inequalities are supplied; rational Möbius invertibility proves β irrational and the two displayed root identities. This is the final algebraic step of root reduction.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, final paragraph of found:reduce-roots

import Definitions.Def_Freiman_reducedForms
import Definitions.Def_Freiman_rootConvergentData

namespace Freiman

theorem form_root_coordinate_algebra (r s : ℝ) (hs : Irrational s) (D : RootConvergentData r) (n : ℕ) (h : secondRootCoordinate D s n ∈ Set.Ioo (-1 : ℝ) 0) :
    ∃ a b c d : ℤ, ∃ α β : ℝ, formUnimodular a b c d ∧
      1 < α ∧ 0 < β ∧ β < 1 ∧ Irrational α ∧ Irrational β ∧
      (c:ℝ)*α+(d:ℝ) ≠ 0 ∧ -(c:ℝ)*β+(d:ℝ) ≠ 0 ∧
      r = ((a:ℝ)*α+(b:ℝ))/((c:ℝ)*α+(d:ℝ)) ∧
      s = (-(a:ℝ)*β+(b:ℝ))/(-(c:ℝ)*β+(d:ℝ)) := by
  sorry

end Freiman
