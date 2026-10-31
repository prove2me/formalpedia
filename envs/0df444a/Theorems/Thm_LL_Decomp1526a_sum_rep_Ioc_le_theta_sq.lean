-- Prove2me | Theorems.Thm_LL_Decomp1526a_sum_rep_Ioc_le_theta_sq
-- name    : LL_Decomp1526a.sum_rep_Ioc_le_theta_sq
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:04:57.770305+00:00
-- url     : https://prove2.me/theorems/31888c06-3454-476c-a6e0-a334bf1836f6
-- title:
--   Crude upper bound for the first moment
-- statement:
--   For all natural numbers $a,b$, $\sum_{N\in\,]a,b]} r(N)\le\theta(b)^2$, where $\theta$ is the first Chebyshev function.
-- source:
--   Elementary, from the definition of $r$.

import Mathlib
import Definitions.Def_LL_Decomp1526a_rep

open Finset Real
open scoped Chebyshev Classical

namespace LL_Decomp1526a
theorem sum_rep_Ioc_le_theta_sq (a b : ℕ) :
    ∑ N ∈ Ioc a b, rep N ≤ θ (b : ℝ) ^ 2 := by sorry
end LL_Decomp1526a
