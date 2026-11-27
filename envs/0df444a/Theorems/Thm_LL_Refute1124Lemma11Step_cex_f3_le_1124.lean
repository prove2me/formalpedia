-- Prove2me | Theorems.Thm_LL_Refute1124Lemma11Step_cex_f3_le_1124
-- name    : LL_Refute1124Lemma11Step.cex_f3_le_1124
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-27T05:47:29.619001+00:00
-- url     : https://prove2.me/theorems/c26aa06b-8cfa-5239-8c75-bc17f6d07c43
-- title:
--   $f_3(1)\le 2/5$ for the linear sieve function $f_3$
-- statement:
--   The value at $s=1$ of the third linear sieve function satisfies $f_3(1)\le 2/5$; numerically $f_3(1)\approx 0.29364$.
-- source:
--   Bordignon, Johnston and Starichkova, arXiv 2207.09452v6, displays 15 to 17, page 6.

import Mathlib
import Definitions.Def_LL_Refute1124Lemma11Step_bjsF306

open Finset Real

namespace LL_Refute1124Lemma11Step
theorem cex_f3_le_1124 : bjsF306 3 1 ≤ 2 / 5 := by sorry
end LL_Refute1124Lemma11Step
