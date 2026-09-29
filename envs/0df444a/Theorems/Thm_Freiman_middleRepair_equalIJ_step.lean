-- Prove2me | Theorems.Thm_Freiman_middleRepair_equalIJ_step
-- name    : Freiman.middleRepair_equalIJ_step
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:30:46.336021+00:00
-- url     : https://prove2.me/theorems/2c18b30b-29e9-4c9b-96f4-ba7d31c1cbfb
-- title:
--   Report convention repair: middleRepair_equalIJ_step
-- statement:
--   Combine the independently checkable data for row equalIJ into a compatible target-preserving subdivision, with the all-3 completion included in essential J rows. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, row equalIJ and m2b:prop:path Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_equalIJ_step :
    ∀ (c : MiddleCore) (t : ℝ), middleRegular c → middleRepairGood c → middleRowCondition c .equalIJ → t∈middleCover c →
      middleRealized c t ∨ ∃ d : MiddleCore, middleRegular d ∧ middleRepairGood d ∧ middleRepairProper c d ∧ t∈middleCover d := by
  sorry
