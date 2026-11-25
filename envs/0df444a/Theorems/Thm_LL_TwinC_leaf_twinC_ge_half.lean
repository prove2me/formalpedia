-- Prove2me | Theorems.Thm_LL_TwinC_leaf_twinC_ge_half
-- name    : LL_TwinC.leaf_twinC_ge_half
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-25T04:06:35.026284+00:00
-- url     : https://prove2.me/theorems/fd192487-e2a7-4660-9f56-1ef2803a01c6
-- title:
--   $C_2\ge1/2$
-- statement:
--   The twin prime constant $C_2=\prod_{p>2}\bigl(1-1/(p-1)^2\bigr)$, product over the odd primes, satisfies $1/2\le C_2$.
-- source:
--   Equation 2 of M. Bordignon, D. R. Johnston and V. Starichkova, An explicit version of Chen's theorem, arXiv:2207.09452.

import Mathlib
import Definitions.Def_LL_TwinC_twinC

namespace LL_TwinC
theorem leaf_twinC_ge_half : (1 : ℝ) / 2 ≤ twinC := by sorry
end LL_TwinC
