-- Prove2me | Theorems.Thm_Freiman_section14_s0010_plan0007_valid
-- name    : Freiman.section14_s0010_plan0007_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T18:22:48.336522+00:00
-- url     : https://prove2.me/theorems/e8f0bc5f-5240-4fdf-8e15-eff3c9b512a0
-- title:
--   Freiman.section14_s0010_plan0007_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 10).plans.drop 7).take 1, section14PlanValid section14Catalog (section14State section14Catalog 10) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_plan0007_valid : ∀ p ∈ ((section14State section14Catalog 10).plans.drop 7).take 1, section14PlanValid section14Catalog (section14State section14Catalog 10) p := by sorry
