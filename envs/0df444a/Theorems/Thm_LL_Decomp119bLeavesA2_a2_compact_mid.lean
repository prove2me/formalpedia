-- Prove2me | Theorems.Thm_LL_Decomp119bLeavesA2_a2_compact_mid
-- name    : LL_Decomp119bLeavesA2.a2_compact_mid
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-24T17:00:12.277739+00:00
-- url     : https://prove2.me/theorems/3520a5a2-4fc9-4fd8-87a6-fa54f8ffaa37
-- title:
--   Lemma A.2 on $0\le\delta\le 655$
-- statement:
--   For every real $\delta$ with $0\le\delta\le 655$, $|(-2\pi i\delta)^2\,\widehat{\eta_2}(\delta)|\le 31.521$.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach's problem, arXiv:1205.5252, Lemma A.2, pages 74 and 75

import Mathlib
import Definitions.Def_LL_Decomp119bLeavesA2_e
import Definitions.Def_LL_Decomp119bLeavesA2_fhat
import Definitions.Def_LL_Decomp119bLeavesA2_eta2

open MeasureTheory Set Real

namespace LL_Decomp119bLeavesA2
theorem a2_compact_mid (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 655) :
    ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ‖ ≤ 31.521 := by sorry
end LL_Decomp119bLeavesA2
