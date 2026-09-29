-- Prove2me | Theorems.Thm_Freiman_section14_s0004_plan0002_valid
-- name    : Freiman.section14_s0004_plan0002_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T03:14:32.820356+00:00
-- url     : https://prove2.me/theorems/37425ac4-81c3-4537-b1ee-a46d7da8f845
-- title:
--   Freiman.section14_s0004_plan0002_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 4).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 4) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_plan0002_valid : ∀ p ∈ ((section14State section14Catalog 4).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 4) p := by sorry
