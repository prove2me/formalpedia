-- Prove2me | Theorems.Thm_LL_SchoenfeldLiS76_piece_16_32
-- name    : LL_SchoenfeldLiS76.piece_16_32
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-23T17:37:08.272799+00:00
-- url     : https://prove2.me/theorems/4451199f-1d70-4100-9bb0-153f88ac1135
-- title:
--   Enclosure of $\int_{16}^{32} dt/\log t$ in $[5.0853,5.0855]$
-- statement:
--   The integral $\int_{16}^{32}\frac{dt}{\log t}$ satisfies $5.0853\le\int_{16}^{32}\frac{dt}{\log t}\le5.0855$.
-- source:
--   Schoenfeld 1976, Math. Comp. 30, page 340, direct calculation of (6.18) at $x=2657$, doi:10.1090/S0025-5718-1976-0457374-X; input to Bordignon and Starichkova, arXiv:2211.08844.

import Mathlib

open Real MeasureTheory intervalIntegral Set

namespace LL_SchoenfeldLiS76
theorem piece_16_32 : 5.0853 ≤ (∫ t in (16 : ℝ)..32, 1 / log t) ∧
    (∫ t in (16 : ℝ)..32, 1 / log t) ≤ 5.0855 := by sorry
end LL_SchoenfeldLiS76
