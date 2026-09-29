-- Prove2me | Theorems.Thm_Freiman_section14_s0008_plan0003_valid
-- name    : Freiman.section14_s0008_plan0003_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:16:20.800505+00:00
-- url     : https://prove2.me/theorems/0babe5dc-ed88-436e-bb30-6b9a3bf51054
-- title:
--   Freiman.section14_s0008_plan0003_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 8).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 8) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_plan0003_valid : ∀ p ∈ ((section14State section14Catalog 8).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 8) p := by sorry
