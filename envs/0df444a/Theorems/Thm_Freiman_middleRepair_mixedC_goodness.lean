-- Prove2me | Theorems.Thm_Freiman_middleRepair_mixedC_goodness
-- name    : Freiman.middleRepair_mixedC_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:45.641153+00:00
-- url     : https://prove2.me/theorems/58fc94f2-c44b-4389-a6cf-c94f1901a48e
-- title:
--   Report convention repair: middleRepair_mixedC_goodness
-- statement:
--   Child goodness in row mixedC, with all normalization and shortening alternatives. This does not assume a descendant has ratio below 19/5. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:prop:opposite, case C Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_mixedC_goodness :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .mixedC → ∀ d ∈ middleRepairRowChildren c .mixedC, middleRepairGood d := by
  sorry
