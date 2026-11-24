-- Prove2me | Theorems.Thm_LL_Decomp119bLeavesA2_a2_grid_certificate
-- name    : LL_Decomp119bLeavesA2.a2_grid_certificate
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-24T16:29:54.620206+00:00
-- url     : https://prove2.me/theorems/223273d4-8394-4a42-a5b2-6615fd0d0329
-- title:
--   Grid values at $\delta=k/1000$ are at most $31.520695$
-- statement:
--   For every natural number $k\le 655000$, $|(-2\pi i\,k/1000)^2\,\widehat{\eta_2}(k/1000)|\le 31.520695$. The largest grid value is about $31.5206507$, at $k=17415$.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach's problem, arXiv:1205.5252, Lemma A.2, pages 74 and 75

import Mathlib
import Definitions.Def_LL_Decomp119bLeavesA2_e
import Definitions.Def_LL_Decomp119bLeavesA2_fhat
import Definitions.Def_LL_Decomp119bLeavesA2_eta2

open MeasureTheory Set Real

namespace LL_Decomp119bLeavesA2
theorem a2_grid_certificate (k : ℕ) (hk : k ≤ 655000) :
    ‖(-2 * π * Complex.I * ((k / 1000 : ℝ) : ℂ)) ^ 2 * fhat eta2 (k / 1000 : ℝ)‖ ≤ 31.520695 := by sorry
end LL_Decomp119bLeavesA2
