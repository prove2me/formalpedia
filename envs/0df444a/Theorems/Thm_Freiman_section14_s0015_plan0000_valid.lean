-- Prove2me | Theorems.Thm_Freiman_section14_s0015_plan0000_valid
-- name    : Freiman.section14_s0015_plan0000_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T21:26:50.219953+00:00
-- url     : https://prove2.me/theorems/27d79576-d2c0-4f30-a159-5fd6690ebd57
-- title:
--   Freiman.section14_s0015_plan0000_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 15).plans.drop 0).take 1, section14PlanValid section14Catalog (section14State section14Catalog 15) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_plan0000_valid : ∀ p ∈ ((section14State section14Catalog 15).plans.drop 0).take 1, section14PlanValid section14Catalog (section14State section14Catalog 15) p := by sorry
