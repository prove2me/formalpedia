-- Prove2me | Theorems.Thm_LL_SchoenfeldLiS76_piece_128_256
-- name    : LL_SchoenfeldLiS76.piece_128_256
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-23T17:37:49.080308+00:00
-- url     : https://prove2.me/theorems/3755804e-6046-4954-b406-d42757121af1
-- title:
--   Enclosure of $\int_{128}^{256} dt/\log t$ in $[24.4704,24.4706]$
-- statement:
--   The integral $\int_{128}^{256}\frac{dt}{\log t}$ satisfies $24.4704\le\int_{128}^{256}\frac{dt}{\log t}\le24.4706$.
-- source:
--   Schoenfeld 1976, Math. Comp. 30, page 340, direct calculation of (6.18) at $x=2657$, doi:10.1090/S0025-5718-1976-0457374-X; input to Bordignon and Starichkova, arXiv:2211.08844.

import Mathlib

open Real MeasureTheory intervalIntegral Set

namespace LL_SchoenfeldLiS76
theorem piece_128_256 : 24.4704 ≤ (∫ t in (128 : ℝ)..256, 1 / log t) ∧
    (∫ t in (128 : ℝ)..256, 1 / log t) ≤ 24.4706 := by sorry
end LL_SchoenfeldLiS76
