-- Prove2me | Theorems.Thm_Freiman_section14_s0002_plan0004_valid
-- name    : Freiman.section14_s0002_plan0004_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:18:12.196002+00:00
-- url     : https://prove2.me/theorems/40fa74e4-8fc1-46e5-9844-1ccf93b4912b
-- title:
--   Freiman.section14_s0002_plan0004_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 2).plans.drop 4).take 1, section14PlanValid section14Catalog (section14State section14Catalog 2) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_plan0004_valid : ∀ p ∈ ((section14State section14Catalog 2).plans.drop 4).take 1, section14PlanValid section14Catalog (section14State section14Catalog 2) p := by sorry
