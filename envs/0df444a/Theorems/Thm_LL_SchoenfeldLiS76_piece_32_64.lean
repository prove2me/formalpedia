-- Prove2me | Theorems.Thm_LL_SchoenfeldLiS76_piece_32_64
-- name    : LL_SchoenfeldLiS76.piece_32_64
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-23T17:37:24.353402+00:00
-- url     : https://prove2.me/theorems/4b3423c7-999c-4b17-85ef-43bf8e735741
-- title:
--   Enclosure of $\int_{32}^{64} dt/\log t$ in $[8.3295,8.3297]$
-- statement:
--   The integral $\int_{32}^{64}\frac{dt}{\log t}$ satisfies $8.3295\le\int_{32}^{64}\frac{dt}{\log t}\le8.3297$.
-- source:
--   Schoenfeld 1976, Math. Comp. 30, page 340, direct calculation of (6.18) at $x=2657$, doi:10.1090/S0025-5718-1976-0457374-X; input to Bordignon and Starichkova, arXiv:2211.08844.

import Mathlib

open Real MeasureTheory intervalIntegral Set

namespace LL_SchoenfeldLiS76
theorem piece_32_64 : 8.3295 ≤ (∫ t in (32 : ℝ)..64, 1 / log t) ∧
    (∫ t in (32 : ℝ)..64, 1 / log t) ≤ 8.3297 := by sorry
end LL_SchoenfeldLiS76
