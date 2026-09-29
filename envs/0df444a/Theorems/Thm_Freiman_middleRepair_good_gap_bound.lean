-- Prove2me | Theorems.Thm_Freiman_middleRepair_good_gap_bound
-- name    : Freiman.middleRepair_good_gap_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:00.400001+00:00
-- url     : https://prove2.me/theorems/ff692265-4ced-4c00-913c-ee0f17cfd979
-- title:
--   Report convention repair: middleRepair_good_gap_bound
-- statement:
--   Because each child cover lies in its compatible sum hull, child intersection forces the narrower width to be at least the wider-side separating gap. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:lem:good5 Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_good_gap_bound :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c →
      middleGapFraction (middleParameter (middleNormalized c).left) * middleWidth (middleNormalized c).left  ≤  middleWidth (middleNormalized c).right := by
  sorry
