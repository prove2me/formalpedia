-- Prove2me | Theorems.Thm_LL_Decomp1526a_rep_of_odd
-- name    : LL_Decomp1526a.rep_of_odd
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:04:01.246791+00:00
-- url     : https://prove2.me/theorems/3fd7237c-786b-4875-950d-2cb1e6495ed1
-- title:
--   Representation function at odd arguments
-- statement:
--   For every natural number $N$ that is not even, $r(N)=2\log 2\cdot\log(N-2)$ if $N-2$ is prime, and $r(N)=0$ otherwise, where $N-2$ is natural subtraction.
-- source:
--   Elementary consequence of the definition of $r$; used in Ramaré 1995, Section 2.3, p. 653.

import Mathlib
import Definitions.Def_LL_Decomp1526a_rep

open Finset Real
open scoped Chebyshev Classical

namespace LL_Decomp1526a
theorem rep_of_odd {N : ℕ} (hN : ¬ Even N) :
    rep N = if (N - 2).Prime then 2 * Real.log 2 * Real.log ((N - 2 : ℕ) : ℝ) else 0 := by sorry
end LL_Decomp1526a
