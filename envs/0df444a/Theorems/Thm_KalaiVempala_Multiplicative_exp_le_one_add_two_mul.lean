-- Prove2me | Theorems.Thm_KalaiVempala_Multiplicative_exp_le_one_add_two_mul
-- name    : KalaiVempala.Multiplicative.exp_le_one_add_two_mul
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:23.677591+00:00
-- url     : https://prove2.me/theorems/b6fe7a62-66d1-4a90-8379-a0c0aa959d88
-- title:
--   P. 303 — for ε ≤ 1/A, e^{εA} ≤ 1 + 2εA
-- statement:
--   Let $A > 0$ and $0 < \varepsilon \le 1/A$. Then
--   $$e^{\varepsilon A} \;\le\; 1 + 2\varepsilon A .$$
--
--   This elementary estimate turns the per-period factor $e^{\varepsilon A}$ of (6) into the factor $1 + 2\varepsilon A$ of the combined bound for FPL\*(ε).
--
--   **Formalization Note** The hypotheses $\varepsilon > 0$ and $A > 0$ make "$\varepsilon \le 1/A$" meaningful (in Lean $1/0 = 0$).
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 303, proof of Theorem 1.1(b), the sentence 'For ε ≤ 1/A, e^{εA} ≤ 1 + 2εA'

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Multiplicative_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Multiplicative

theorem exp_le_one_add_two_mul (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A)
    (h : ε ≤ 1 / A) : Real.exp (ε * A) ≤ 1 + 2 * ε * A := by sorry

end KalaiVempala.Multiplicative
