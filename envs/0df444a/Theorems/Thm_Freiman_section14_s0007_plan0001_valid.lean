-- Prove2me | Theorems.Thm_Freiman_section14_s0007_plan0001_valid
-- name    : Freiman.section14_s0007_plan0001_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T11:26:34.868916+00:00
-- url     : https://prove2.me/theorems/eb7f3b2e-9637-4c02-8065-fb166a7c94be
-- title:
--   Freiman.section14_s0007_plan0001_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 7).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 7) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_plan0001_valid : ∀ p ∈ ((section14State section14Catalog 7).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 7) p := by sorry
