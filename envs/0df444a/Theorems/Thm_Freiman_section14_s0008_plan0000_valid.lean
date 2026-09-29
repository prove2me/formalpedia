-- Prove2me | Theorems.Thm_Freiman_section14_s0008_plan0000_valid
-- name    : Freiman.section14_s0008_plan0000_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:16:56.196682+00:00
-- url     : https://prove2.me/theorems/e7df9541-ba71-44d4-b921-e4880354bb2b
-- title:
--   Freiman.section14_s0008_plan0000_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 8).plans.drop 0).take 1, section14PlanValid section14Catalog (section14State section14Catalog 8) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_plan0000_valid : ∀ p ∈ ((section14State section14Catalog 8).plans.drop 0).take 1, section14PlanValid section14Catalog (section14State section14Catalog 8) p := by sorry
