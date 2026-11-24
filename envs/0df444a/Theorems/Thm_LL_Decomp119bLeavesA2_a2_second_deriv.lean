-- Prove2me | Theorems.Thm_LL_Decomp119bLeavesA2_a2_second_deriv
-- name    : LL_Decomp119bLeavesA2.a2_second_deriv
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-24T16:16:30.204586+00:00
-- url     : https://prove2.me/theorems/52360d9c-35f8-4db3-b3c2-9ddbac39114b
-- title:
--   Second derivative bound $48\pi^2$
-- statement:
--   For every real $v$, the second derivative at $v$ of $t\mapsto(-2\pi i t)^2\widehat{\eta_2}(t)$ has norm at most $48\pi^2$.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach's problem, arXiv:1205.5252, Lemma A.2, pages 74 and 75

import Mathlib
import Definitions.Def_LL_Decomp119bLeavesA2_e
import Definitions.Def_LL_Decomp119bLeavesA2_fhat
import Definitions.Def_LL_Decomp119bLeavesA2_eta2

open MeasureTheory Set Real

namespace LL_Decomp119bLeavesA2
theorem a2_second_deriv (v : ℝ) :
    ‖deriv (deriv (fun t : ℝ => (-2 * π * Complex.I * (t : ℂ)) ^ 2 * fhat eta2 t)) v‖ ≤
      48 * π ^ 2 := by sorry
end LL_Decomp119bLeavesA2
