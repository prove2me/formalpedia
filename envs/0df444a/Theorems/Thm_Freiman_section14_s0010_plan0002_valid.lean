-- Prove2me | Theorems.Thm_Freiman_section14_s0010_plan0002_valid
-- name    : Freiman.section14_s0010_plan0002_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T18:15:56.545092+00:00
-- url     : https://prove2.me/theorems/c556faea-a8d3-4a11-a357-a5383f785942
-- title:
--   Freiman.section14_s0010_plan0002_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 10).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 10) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_plan0002_valid : ∀ p ∈ ((section14State section14Catalog 10).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 10) p := by sorry
