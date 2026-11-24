-- Prove2me | Theorems.Thm_LL_SchoenfeldLiS76_piece_8_16
-- name    : LL_SchoenfeldLiS76.piece_8_16
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-23T17:36:53.465097+00:00
-- url     : https://prove2.me/theorems/a6252132-872a-41fa-bc47-33a56fb8370d
-- title:
--   Enclosure of $\int_{8}^{16} dt/\log t$ in $[3.2659,3.2661]$
-- statement:
--   The integral $\int_{8}^{16}\frac{dt}{\log t}$ satisfies $3.2659\le\int_{8}^{16}\frac{dt}{\log t}\le3.2661$.
-- source:
--   Schoenfeld 1976, Math. Comp. 30, page 340, direct calculation of (6.18) at $x=2657$, doi:10.1090/S0025-5718-1976-0457374-X; input to Bordignon and Starichkova, arXiv:2211.08844.

import Mathlib

open Real MeasureTheory intervalIntegral Set

namespace LL_SchoenfeldLiS76
theorem piece_8_16 : 3.2659 ≤ (∫ t in (8 : ℝ)..16, 1 / log t) ∧
    (∫ t in (8 : ℝ)..16, 1 / log t) ≤ 3.2661 := by sorry
end LL_SchoenfeldLiS76
