-- Prove2me | Theorems.Thm_LL_Decomp1528a_log4_add_le_three
-- name    : LL_Decomp1528a.log4_add_le_three
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:14:56.885623+00:00
-- url     : https://prove2.me/theorems/b6001e98-4d01-4cf4-9a29-6ff0248742ff
-- title:
--   Uniform logarithmic bound with a square-root denominator
-- statement:
--   For every real number $t\ge1$, $\log4+\frac{2\log t}{\sqrt t}\le3$.
-- source:
--   Elementary real inequality in lab unit U-1528, used with the Chebyshev psi estimate. Source context: https://arxiv.org/abs/2608.09488v1

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528a
theorem log4_add_le_three {t : ℝ} (ht : 1 ≤ t) : log 4 + 2 * log t / √t ≤ 3 := by sorry
end LL_Decomp1528a
