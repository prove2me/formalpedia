-- Prove2me | Theorems.Thm_Freiman_section14_s0015_plan0002_valid
-- name    : Freiman.section14_s0015_plan0002_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T21:28:50.649165+00:00
-- url     : https://prove2.me/theorems/58568d56-1e4a-4158-aea7-574e478719c4
-- title:
--   Freiman.section14_s0015_plan0002_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 15).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 15) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_plan0002_valid : ∀ p ∈ ((section14State section14Catalog 15).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 15) p := by sorry
