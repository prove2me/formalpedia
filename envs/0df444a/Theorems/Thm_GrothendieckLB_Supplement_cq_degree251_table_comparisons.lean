-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_degree251_table_comparisons
-- name    : GrothendieckLB.Supplement.cq_degree251_table_comparisons
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T20:31:09.028071+00:00
-- url     : https://prove2.me/theorems/4dde44f3-dd3e-427e-baf8-4e08631935bd
-- title:
--   All 125 rounded comparisons on the degree-251 cubic–quintic tables
-- statement:
--   The integer interval convolution on the packed coefficient tables satisfies all 125 prescribed upper bounds. A base-$2^{320}$ polynomial evaluation checks the unrounded central sums, and an explicit error estimate accounts for every outward rounding.
-- source:
--   The fixed-point verifier of Prove2Me submission 6ced4b79-2df5-46cd-91cc-4b3d293f1114 for the cubic–quintic correlation of Saha et al., arXiv:2608.11158v2.

import Definitions.Def_GrothendieckLB_Supplement_cqDegree251Tables

namespace GrothendieckLB.Supplement

theorem cq_degree251_table_comparisons :
    ∀ j : Fin 125,
      let v := CQHeadArithmetic.fullSum CQDegree251.weights CQDegree251.powers (2*j.val+3)
      max (-v.lo) v.hi * 10^40 ≤
        CQHeadArithmetic.coefficientScale*2*314159265358979323846*(cqHeadUnits[j.val]?.getD 0) := by sorry

end GrothendieckLB.Supplement
