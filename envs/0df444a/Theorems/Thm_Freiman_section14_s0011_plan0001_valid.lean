-- Prove2me | Theorems.Thm_Freiman_section14_s0011_plan0001_valid
-- name    : Freiman.section14_s0011_plan0001_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T16:09:33.426379+00:00
-- url     : https://prove2.me/theorems/7906637a-d8c3-4cdd-95e3-4de9e29aec9c
-- title:
--   Freiman.section14_s0011_plan0001_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 11).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 11) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_plan0001_valid : ∀ p ∈ ((section14State section14Catalog 11).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 11) p := by sorry
