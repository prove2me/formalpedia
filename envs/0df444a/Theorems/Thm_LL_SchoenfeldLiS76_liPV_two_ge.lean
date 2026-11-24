-- Prove2me | Theorems.Thm_LL_SchoenfeldLiS76_liPV_two_ge
-- name    : LL_SchoenfeldLiS76.liPV_two_ge
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-23T17:39:17.553803+00:00
-- url     : https://prove2.me/theorems/322d51c1-71d4-4896-a8f0-f704aa743642
-- title:
--   Lower bound $\operatorname{li}(2)\ge 1.045$
-- statement:
--   The principal value logarithmic integral satisfies $\operatorname{li}(2)\ge 1.045$.
-- source:
--   Schoenfeld 1976, Math. Comp. 30, page 340, direct calculation of (6.18) at $x=2657$, doi:10.1090/S0025-5718-1976-0457374-X; input to Bordignon and Starichkova, arXiv:2211.08844.

import Mathlib
import Definitions.Def_LL_SchoenfeldLiS76_liPart
import Definitions.Def_LL_SchoenfeldLiS76_liPV

open Real MeasureTheory intervalIntegral Set

namespace LL_SchoenfeldLiS76
theorem liPV_two_ge : 1.045 ≤ liPV 2 := by sorry
end LL_SchoenfeldLiS76
