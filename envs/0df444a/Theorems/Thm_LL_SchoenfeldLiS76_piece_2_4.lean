-- Prove2me | Theorems.Thm_LL_SchoenfeldLiS76_piece_2_4
-- name    : LL_SchoenfeldLiS76.piece_2_4
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-23T17:36:16.091737+00:00
-- url     : https://prove2.me/theorems/0404dc3e-187c-405b-950b-dbbfff3606d5
-- title:
--   Enclosure of $\int_{2}^{4} dt/\log t$ in $[1.9223,1.9225]$
-- statement:
--   The integral $\int_{2}^{4}\frac{dt}{\log t}$ satisfies $1.9223\le\int_{2}^{4}\frac{dt}{\log t}\le1.9225$.
-- source:
--   Schoenfeld 1976, Math. Comp. 30, page 340, direct calculation of (6.18) at $x=2657$, doi:10.1090/S0025-5718-1976-0457374-X; input to Bordignon and Starichkova, arXiv:2211.08844.

import Mathlib

open Real MeasureTheory intervalIntegral Set

namespace LL_SchoenfeldLiS76
theorem piece_2_4 : 1.9223 ≤ (∫ t in (2 : ℝ)..4, 1 / log t) ∧
    (∫ t in (2 : ℝ)..4, 1 / log t) ≤ 1.9225 := by sorry
end LL_SchoenfeldLiS76
