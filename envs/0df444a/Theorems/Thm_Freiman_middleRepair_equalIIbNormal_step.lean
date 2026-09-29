-- Prove2me | Theorems.Thm_Freiman_middleRepair_equalIIbNormal_step
-- name    : Freiman.middleRepair_equalIIbNormal_step
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:30:38.991989+00:00
-- url     : https://prove2.me/theorems/3a495892-0e1e-4d6d-bb1f-a4be5ec2b022
-- title:
--   Report convention repair: middleRepair_equalIIbNormal_step
-- statement:
--   Combine the independently checkable data for row equalIIbNormal into a compatible target-preserving subdivision, with the all-3 completion included in essential J rows. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, row equalIIbNormal and m2b:prop:path Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_equalIIbNormal_step :
    ∀ (c : MiddleCore) (t : ℝ), middleRegular c → middleRepairGood c → middleRowCondition c .equalIIbNormal → t∈middleCover c →
      middleRealized c t ∨ ∃ d : MiddleCore, middleRegular d ∧ middleRepairGood d ∧ middleRepairProper c d ∧ t∈middleCover d := by
  sorry
