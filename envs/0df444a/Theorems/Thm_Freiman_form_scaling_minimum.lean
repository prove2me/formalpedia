-- Prove2me | Theorems.Thm_Freiman_form_scaling_minimum
-- name    : Freiman.form_scaling_minimum
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:57:56.160449+00:00
-- url     : https://prove2.me/theorems/bb8cc4c9-c712-4ff4-a7b0-620e66b4af7a
-- title:
--   Absolute scaling of the lattice infimum
-- statement:
--   Scaling all coefficients scales every absolute lattice value by the positive number |k|, hence also its infimum.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, opening paragraph

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_scaling_minimum (A B C k : ℝ) (hk : k ≠ 0) :
    quadraticMinimum (k*A) (k*B) (k*C) = |k| * quadraticMinimum A B C := by
  sorry

end Freiman
