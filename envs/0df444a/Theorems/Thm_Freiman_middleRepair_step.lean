-- Prove2me | Theorems.Thm_Freiman_middleRepair_step
-- name    : Freiman.middleRepair_step
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:30:46.012997+00:00
-- url     : https://prove2.me/theorems/804882d8-8570-44bf-b81e-a2b985c8a556
-- title:
--   Report convention repair: middleRepair_step
-- statement:
--   One exact subdivision step retains the same real target and actual physical prefix compatibility, or realizes the target as the explicit J-limit completion. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:prop:path Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_step :
    ∀ (c : MiddleCore) (t : ℝ), middleRegular c → middleRepairGood c → t∈middleCover c →
      middleRealized c t ∨ ∃ d : MiddleCore, middleRegular d ∧ middleRepairGood d ∧ middleRepairProper c d ∧ t∈middleCover d := by
  sorry
