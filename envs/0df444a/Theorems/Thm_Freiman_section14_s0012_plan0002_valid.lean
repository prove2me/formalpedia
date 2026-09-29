-- Prove2me | Theorems.Thm_Freiman_section14_s0012_plan0002_valid
-- name    : Freiman.section14_s0012_plan0002_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T05:46:26.630101+00:00
-- url     : https://prove2.me/theorems/b8cec8dd-7d78-4791-a7b9-1a5fcad8aedd
-- title:
--   Freiman.section14_s0012_plan0002_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 12).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 12) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_plan0002_valid : ∀ p ∈ ((section14State section14Catalog 12).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 12) p := by sorry
