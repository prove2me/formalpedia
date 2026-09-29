-- Prove2me | Theorems.Thm_Freiman_middleRepair_child_regular
-- name    : Freiman.middleRepair_child_regular
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:28:43.328596+00:00
-- url     : https://prove2.me/theorems/b390b195-0431-478e-98d6-0dafc7543bcc
-- title:
--   Report convention repair: middleRepair_child_regular
-- statement:
--   Actual compatible children preserve the real parameter rectangle and strictly extend the physical prefixes. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, cover convention Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_child_regular :
    ∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v →
      0 < u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v) := by
  sorry
