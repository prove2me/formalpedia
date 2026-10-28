-- Prove2me | Theorems.Thm_LL_Linnik1536a_exp_le_even_partial
-- name    : LL_Linnik1536a.exp_le_even_partial
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-27T21:44:52.283402+00:00
-- url     : https://prove2.me/theorems/cf8c8c4e-45e1-4a4a-8ccd-82a276a14ace
-- title:
--   $e^r$ below twice an even partial sum plus one
-- statement:
--   If $0\le r\le A$ and $K=2\lceil A\rceil+1$, then $e^r\le 2\sum_{j<K} r^{2j}/(2j)!+1$.
-- source:
--   J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem, I, Acta Arith. 109 (2003), 169-194, Sections 4 and 7

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
open Real MeasureTheory Finset

namespace LL_Linnik1536a

theorem exp_le_even_partial {A r : ℝ} (hr : 0 ≤ r) (hrA : r ≤ A) :
    Real.exp r ≤
      2 * ∑ j ∈ range (2 * ⌈A⌉₊ + 1), r ^ (2 * j) / ((2 * j).factorial : ℝ) + 1 := by sorry

end LL_Linnik1536a
