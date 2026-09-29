-- Prove2me | Theorems.Thm_Freiman_section14_s0008_plan0006_valid
-- name    : Freiman.section14_s0008_plan0006_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:23:37.780934+00:00
-- url     : https://prove2.me/theorems/347a6861-2bae-4ac0-9c1a-b54e3f0c8504
-- title:
--   Freiman.section14_s0008_plan0006_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 8).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 8) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_plan0006_valid : ∀ p ∈ ((section14State section14Catalog 8).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 8) p := by sorry
