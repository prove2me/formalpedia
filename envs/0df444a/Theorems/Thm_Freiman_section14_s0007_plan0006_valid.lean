-- Prove2me | Theorems.Thm_Freiman_section14_s0007_plan0006_valid
-- name    : Freiman.section14_s0007_plan0006_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T11:32:22.587736+00:00
-- url     : https://prove2.me/theorems/6eb189e3-f73c-4f2a-87e7-eeef6bf47b7f
-- title:
--   Freiman.section14_s0007_plan0006_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 7).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 7) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_plan0006_valid : ∀ p ∈ ((section14State section14Catalog 7).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 7) p := by sorry
