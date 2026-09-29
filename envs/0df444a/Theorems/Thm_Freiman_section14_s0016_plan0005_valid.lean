-- Prove2me | Theorems.Thm_Freiman_section14_s0016_plan0005_valid
-- name    : Freiman.section14_s0016_plan0005_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T01:01:11.318934+00:00
-- url     : https://prove2.me/theorems/7033d391-4298-4503-8328-a30b633c80ad
-- title:
--   Freiman.section14_s0016_plan0005_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 16).plans.drop 5).take 1, section14PlanValid section14Catalog (section14State section14Catalog 16) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_plan0005_valid : ∀ p ∈ ((section14State section14Catalog 16).plans.drop 5).take 1, section14PlanValid section14Catalog (section14State section14Catalog 16) p := by sorry
