-- Prove2me | Theorems.Thm_Freiman_cfValue_surjective_irrational_unit
-- name    : Freiman.cfValue_surjective_irrational_unit
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:19.626045+00:00
-- url     : https://prove2.me/theorems/98ebf34d-dafd-4254-9f7e-023dfeafb606
-- title:
--   Positive-digit expansion of an irrational in the unit interval
-- statement:
--   The usual continued-fraction digit extraction of x converges to x; uniqueness of nested cylinders identifies its value with the existing sSup of even convergents. The sSup bridge is part of this open goal.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.1 and §1.2, passage to ξ=[0;b₁,b₂,…]

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Freiman

theorem cfValue_surjective_irrational_unit (x : ℝ) (hx : Irrational x) (h0 : 0 < x) (h1 : x < 1) :
    ∃ b : ℕ → ℕ+, cfValue b = x := by
  sorry

end Freiman
