-- Prove2me | Theorems.Thm_Freiman_section14_s0012_plan0005_valid
-- name    : Freiman.section14_s0012_plan0005_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T05:52:51.01462+00:00
-- url     : https://prove2.me/theorems/ca4233c5-11fa-4593-b7ea-c9ad005e5824
-- title:
--   Freiman.section14_s0012_plan0005_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 12).plans.drop 5).take 1, section14PlanValid section14Catalog (section14State section14Catalog 12) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_plan0005_valid : ∀ p ∈ ((section14State section14Catalog 12).plans.drop 5).take 1, section14PlanValid section14Catalog (section14State section14Catalog 12) p := by sorry
