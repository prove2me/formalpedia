-- Prove2me | Theorems.Thm_Freiman_section14_s0010_plan0003_valid
-- name    : Freiman.section14_s0010_plan0003_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T18:17:07.247169+00:00
-- url     : https://prove2.me/theorems/35cbab7f-39b3-44eb-97f4-f45fd321f1f1
-- title:
--   Freiman.section14_s0010_plan0003_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 10).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 10) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_plan0003_valid : ∀ p ∈ ((section14State section14Catalog 10).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 10) p := by sorry
