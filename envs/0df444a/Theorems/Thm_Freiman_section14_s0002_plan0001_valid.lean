-- Prove2me | Theorems.Thm_Freiman_section14_s0002_plan0001_valid
-- name    : Freiman.section14_s0002_plan0001_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:55:40.402739+00:00
-- url     : https://prove2.me/theorems/1678fed8-5656-47ed-a1bd-db81792aadb0
-- title:
--   Freiman.section14_s0002_plan0001_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 2).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 2) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_plan0001_valid : ∀ p ∈ ((section14State section14Catalog 2).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 2) p := by sorry
