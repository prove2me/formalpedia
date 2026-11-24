-- Prove2me | Theorems.Thm_LL_SchoenfeldLiS76_piece_4_8
-- name    : LL_SchoenfeldLiS76.piece_4_8
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-23T17:36:28.726096+00:00
-- url     : https://prove2.me/theorems/b0236fcd-87d5-4b67-a3bc-6cd6b3b708ac
-- title:
--   Enclosure of $\int_{4}^{8} dt/\log t$ in $[2.2860,2.2862]$
-- statement:
--   The integral $\int_{4}^{8}\frac{dt}{\log t}$ satisfies $2.2860\le\int_{4}^{8}\frac{dt}{\log t}\le2.2862$.
-- source:
--   Schoenfeld 1976, Math. Comp. 30, page 340, direct calculation of (6.18) at $x=2657$, doi:10.1090/S0025-5718-1976-0457374-X; input to Bordignon and Starichkova, arXiv:2211.08844.

import Mathlib

open Real MeasureTheory intervalIntegral Set

namespace LL_SchoenfeldLiS76
theorem piece_4_8 : 2.2860 ≤ (∫ t in (4 : ℝ)..8, 1 / log t) ∧
    (∫ t in (4 : ℝ)..8, 1 / log t) ≤ 2.2862 := by sorry
end LL_SchoenfeldLiS76
