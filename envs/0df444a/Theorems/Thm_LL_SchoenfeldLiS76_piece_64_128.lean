-- Prove2me | Theorems.Thm_LL_SchoenfeldLiS76_piece_64_128
-- name    : LL_SchoenfeldLiS76.piece_64_128
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-23T17:37:36.698711+00:00
-- url     : https://prove2.me/theorems/bdcaf399-1e86-4377-9930-e924af58aae0
-- title:
--   Enclosure of $\int_{64}^{128} dt/\log t$ in $[14.1078,14.1080]$
-- statement:
--   The integral $\int_{64}^{128}\frac{dt}{\log t}$ satisfies $14.1078\le\int_{64}^{128}\frac{dt}{\log t}\le14.1080$.
-- source:
--   Schoenfeld 1976, Math. Comp. 30, page 340, direct calculation of (6.18) at $x=2657$, doi:10.1090/S0025-5718-1976-0457374-X; input to Bordignon and Starichkova, arXiv:2211.08844.

import Mathlib

open Real MeasureTheory intervalIntegral Set

namespace LL_SchoenfeldLiS76
theorem piece_64_128 : 14.1078 ≤ (∫ t in (64 : ℝ)..128, 1 / log t) ∧
    (∫ t in (64 : ℝ)..128, 1 / log t) ≤ 14.1080 := by sorry
end LL_SchoenfeldLiS76
