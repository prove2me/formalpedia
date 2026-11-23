-- Prove2me | Theorems.Thm_LL_SchoenfeldLiS76_piece_512_1024
-- name    : LL_SchoenfeldLiS76.piece_512_1024
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-23T17:38:14.842283+00:00
-- url     : https://prove2.me/theorems/67b68100-56a3-402b-ad8f-21a0fd79c0ae
-- title:
--   Enclosure of $\int_{512}^{1024} dt/\log t$ in $[77.3568,77.3570]$
-- statement:
--   The integral $\int_{512}^{1024}\frac{dt}{\log t}$ satisfies $77.3568\le\int_{512}^{1024}\frac{dt}{\log t}\le77.3570$.
-- source:
--   Schoenfeld 1976, Math. Comp. 30, page 340, direct calculation of (6.18) at $x=2657$, doi:10.1090/S0025-5718-1976-0457374-X; input to Bordignon and Starichkova, arXiv:2211.08844.

import Mathlib

open Real MeasureTheory intervalIntegral Set

namespace LL_SchoenfeldLiS76
theorem piece_512_1024 : 77.3568 ≤ (∫ t in (512 : ℝ)..1024, 1 / log t) ∧
    (∫ t in (512 : ℝ)..1024, 1 / log t) ≤ 77.3570 := by sorry
end LL_SchoenfeldLiS76
