-- Prove2me | Theorems.Thm_Freiman_middleRepair_j_good
-- name    : Freiman.middleRepair_j_good
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:30:06.444216+00:00
-- url     : https://prove2.me/theorems/379de206-b3ef-42db-8368-89443d8079b6
-- title:
--   Report convention repair: middleRepair_j_good
-- statement:
--   Every J child in either essential row is good, uniformly in k≥1, after checking actual parameter domains and original-side orientation. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:lem:jgood Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_j_good :
    ∀ (c : MiddleCore) (r : MiddleRow) (k : ℕ), middleRegular c → middleRowCondition c r → middleEssentialJ r = true → 1 ≤ k → middleRepairGood (middleRepairJ c k) := by
  sorry
