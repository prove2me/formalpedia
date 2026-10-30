-- Prove2me | Theorems.Thm_LL_Decomp1537b_abs_I1_sub
-- name    : LL_Decomp1537b.abs_I1_sub
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:32:00.911992+00:00
-- url     : https://prove2.me/theorems/b3e0394a-a97a-40ea-a082-c24e5f742d49
-- title:
--   Explicit asymptotic for the difference count
-- statement:
--   For all natural numbers $N,N_1$ and every integer $h$, one has $|I(h)-N|\le|h|+N_1+1$.
-- source:
--   J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem II, Acta Mathematica Hungarica, 2020; Section 2, display (2.17), p. 4

import Mathlib
import Definitions.Def_LL_Decomp1537b_I1

open Finset Real

namespace LL_Decomp1537b
theorem abs_I1_sub (N N1 : ℕ) (h : ℤ) : |(I1 N N1 h : ℝ) - N| ≤ |(h : ℝ)| + N1 + 1 := by sorry
end LL_Decomp1537b
