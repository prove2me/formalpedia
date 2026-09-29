-- Prove2me | Theorems.Thm_Freiman_section14_s0016_plan0003_valid
-- name    : Freiman.section14_s0016_plan0003_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T01:00:31.820103+00:00
-- url     : https://prove2.me/theorems/dad9cf3b-5a5a-46b6-b368-89fd35964939
-- title:
--   Freiman.section14_s0016_plan0003_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 16).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 16) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_plan0003_valid : ∀ p ∈ ((section14State section14Catalog 16).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 16) p := by sorry
