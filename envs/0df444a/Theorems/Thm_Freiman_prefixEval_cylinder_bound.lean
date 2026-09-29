-- Prove2me | Theorems.Thm_Freiman_prefixEval_cylinder_bound
-- name    : Freiman.prefixEval_cylinder_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:48.602998+00:00
-- url     : https://prove2.me/theorems/42b639a6-c7da-4b7d-8e60-fc07be1431bf
-- title:
--   Fibonacci diameter of a continued-fraction cylinder
-- statement:
--   For x,y in [0,1], the two evaluations of a length-m prefix differ by at most 1/F(m+1)^2. The reduction uses the report exact difference identity, positive denominators and Fibonacci denominator lower bound.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, printed p. 7, equations found:continuants and found:continuity and the finite-tail paragraph after found:local-values; §1.2, Theorem 1.3 for the Perron/local comparison.

import Definitions.Def_Freiman_prefixEval
import Mathlib.Data.Nat.Fib.Basic

namespace Freiman

theorem prefixEval_cylinder_bound (w : List ℕ+) (x y : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |prefixEval w x - prefixEval w y| ≤ 1 / ((Nat.fib (w.length + 1) : ℝ) ^ 2) := by
  sorry

end Freiman
