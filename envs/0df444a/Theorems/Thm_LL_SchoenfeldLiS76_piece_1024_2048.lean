-- Prove2me | Theorems.Thm_LL_SchoenfeldLiS76_piece_1024_2048
-- name    : LL_SchoenfeldLiS76.piece_1024_2048
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-23T17:38:26.477617+00:00
-- url     : https://prove2.me/theorems/fb035774-5da7-45cd-923e-c720cf2a9b8a
-- title:
--   Enclosure of $\int_{1024}^{2048} dt/\log t$ in $[140.0363,140.0365]$
-- statement:
--   The integral $\int_{1024}^{2048}\frac{dt}{\log t}$ satisfies $140.0363\le\int_{1024}^{2048}\frac{dt}{\log t}\le140.0365$.
-- source:
--   Schoenfeld 1976, Math. Comp. 30, page 340, direct calculation of (6.18) at $x=2657$, doi:10.1090/S0025-5718-1976-0457374-X; input to Bordignon and Starichkova, arXiv:2211.08844.

import Mathlib

open Real MeasureTheory intervalIntegral Set

namespace LL_SchoenfeldLiS76
theorem piece_1024_2048 : 140.0363 ≤ (∫ t in (1024 : ℝ)..2048, 1 / log t) ∧
    (∫ t in (1024 : ℝ)..2048, 1 / log t) ≤ 140.0365 := by sorry
end LL_SchoenfeldLiS76
