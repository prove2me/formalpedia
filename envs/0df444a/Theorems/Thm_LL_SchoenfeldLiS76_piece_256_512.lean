-- Prove2me | Theorems.Thm_LL_SchoenfeldLiS76_piece_256_512
-- name    : LL_SchoenfeldLiS76.piece_256_512
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-23T17:38:01.7691+00:00
-- url     : https://prove2.me/theorems/5f895a67-7195-4a89-bd62-d47fe877e35b
-- title:
--   Enclosure of $\int_{256}^{512} dt/\log t$ in $[43.2080,43.2082]$
-- statement:
--   The integral $\int_{256}^{512}\frac{dt}{\log t}$ satisfies $43.2080\le\int_{256}^{512}\frac{dt}{\log t}\le43.2082$.
-- source:
--   Schoenfeld 1976, Math. Comp. 30, page 340, direct calculation of (6.18) at $x=2657$, doi:10.1090/S0025-5718-1976-0457374-X; input to Bordignon and Starichkova, arXiv:2211.08844.

import Mathlib

open Real MeasureTheory intervalIntegral Set

namespace LL_SchoenfeldLiS76
theorem piece_256_512 : 43.2080 ≤ (∫ t in (256 : ℝ)..512, 1 / log t) ∧
    (∫ t in (256 : ℝ)..512, 1 / log t) ≤ 43.2082 := by sorry
end LL_SchoenfeldLiS76
