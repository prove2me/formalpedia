-- Prove2me | Theorems.Thm_LL_SchoenfeldLiS76_piece_2048_2657
-- name    : LL_SchoenfeldLiS76.piece_2048_2657
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-23T17:38:39.090234+00:00
-- url     : https://prove2.me/theorems/1b51d861-f634-4104-b46c-d54ee3de152d
-- title:
--   Enclosure of $\int_{2048}^{2657} dt/\log t$ in $[78.4823,78.4825]$
-- statement:
--   The integral $\int_{2048}^{2657}\frac{dt}{\log t}$ satisfies $78.4823\le\int_{2048}^{2657}\frac{dt}{\log t}\le78.4825$.
-- source:
--   Schoenfeld 1976, Math. Comp. 30, page 340, direct calculation of (6.18) at $x=2657$, doi:10.1090/S0025-5718-1976-0457374-X; input to Bordignon and Starichkova, arXiv:2211.08844.

import Mathlib

open Real MeasureTheory intervalIntegral Set

namespace LL_SchoenfeldLiS76
theorem piece_2048_2657 : 78.4823 ≤ (∫ t in (2048 : ℝ)..2657, 1 / log t) ∧
    (∫ t in (2048 : ℝ)..2657, 1 / log t) ≤ 78.4825 := by sorry
end LL_SchoenfeldLiS76
