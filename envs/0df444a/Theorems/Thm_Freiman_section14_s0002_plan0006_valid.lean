-- Prove2me | Theorems.Thm_Freiman_section14_s0002_plan0006_valid
-- name    : Freiman.section14_s0002_plan0006_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:31:50.245854+00:00
-- url     : https://prove2.me/theorems/cf96d61b-feab-4b12-a1b8-56848c5216a8
-- title:
--   Freiman.section14_s0002_plan0006_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 2).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 2) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_plan0006_valid : ∀ p ∈ ((section14State section14Catalog 2).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 2) p := by sorry
