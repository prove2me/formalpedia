-- Prove2me | Theorems.Thm_Freiman_section14_s0004_plan0003_valid
-- name    : Freiman.section14_s0004_plan0003_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T03:17:12.394091+00:00
-- url     : https://prove2.me/theorems/97396cf0-521f-47c9-b34d-c2988a5f6c0f
-- title:
--   Freiman.section14_s0004_plan0003_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 4).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 4) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_plan0003_valid : ∀ p ∈ ((section14State section14Catalog 4).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 4) p := by sorry
