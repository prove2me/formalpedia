-- Prove2me | Theorems.Thm_Freiman_section14_s0008_plan0002_valid
-- name    : Freiman.section14_s0008_plan0002_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:14:59.850858+00:00
-- url     : https://prove2.me/theorems/e0068082-922a-477d-9420-2467e32f8693
-- title:
--   Freiman.section14_s0008_plan0002_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 8).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 8) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_plan0002_valid : ∀ p ∈ ((section14State section14Catalog 8).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 8) p := by sorry
