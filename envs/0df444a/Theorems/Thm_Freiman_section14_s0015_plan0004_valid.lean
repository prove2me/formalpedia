-- Prove2me | Theorems.Thm_Freiman_section14_s0015_plan0004_valid
-- name    : Freiman.section14_s0015_plan0004_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T21:35:26.450966+00:00
-- url     : https://prove2.me/theorems/cff77199-b39c-4d34-93c0-6d2734bad7de
-- title:
--   Freiman.section14_s0015_plan0004_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 15).plans.drop 4).take 1, section14PlanValid section14Catalog (section14State section14Catalog 15) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_plan0004_valid : ∀ p ∈ ((section14State section14Catalog 15).plans.drop 4).take 1, section14PlanValid section14Catalog (section14State section14Catalog 15) p := by sorry
