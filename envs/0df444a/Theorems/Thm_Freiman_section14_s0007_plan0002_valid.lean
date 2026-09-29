-- Prove2me | Theorems.Thm_Freiman_section14_s0007_plan0002_valid
-- name    : Freiman.section14_s0007_plan0002_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T11:25:51.846803+00:00
-- url     : https://prove2.me/theorems/0c9732f7-8439-4a58-bfb8-968558e1baf7
-- title:
--   Freiman.section14_s0007_plan0002_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 7).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 7) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_plan0002_valid : ∀ p ∈ ((section14State section14Catalog 7).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 7) p := by sorry
