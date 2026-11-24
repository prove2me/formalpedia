-- Prove2me | Theorems.Thm_LL_Decomp119bLeavesA2_a2_contDiff
-- name    : LL_Decomp119bLeavesA2.a2_contDiff
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-24T16:03:02.684974+00:00
-- url     : https://prove2.me/theorems/80a824e3-c279-4dd5-8d4f-69f2effed175
-- title:
--   Smoothness of $(-2\pi i t)^2\widehat{\eta_2}(t)$
-- statement:
--   The function $t\mapsto(-2\pi i t)^2\,\widehat{\eta_2}(t)$ from $\mathbb R$ to $\mathbb C$ is twice continuously differentiable.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach's problem, arXiv:1205.5252, Lemma A.2, pages 74 and 75

import Mathlib
import Definitions.Def_LL_Decomp119bLeavesA2_e
import Definitions.Def_LL_Decomp119bLeavesA2_fhat
import Definitions.Def_LL_Decomp119bLeavesA2_eta2

open MeasureTheory Set Real

namespace LL_Decomp119bLeavesA2
theorem a2_contDiff :
    ContDiff ℝ 2 (fun t : ℝ => (-2 * π * Complex.I * (t : ℂ)) ^ 2 * fhat eta2 t) := by sorry
end LL_Decomp119bLeavesA2
