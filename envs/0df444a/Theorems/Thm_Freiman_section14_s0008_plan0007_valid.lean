-- Prove2me | Theorems.Thm_Freiman_section14_s0008_plan0007_valid
-- name    : Freiman.section14_s0008_plan0007_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:24:51.538541+00:00
-- url     : https://prove2.me/theorems/95423e89-098a-48be-b7f6-8577f66acf35
-- title:
--   Freiman.section14_s0008_plan0007_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 8).plans.drop 7).take 1, section14PlanValid section14Catalog (section14State section14Catalog 8) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_plan0007_valid : ∀ p ∈ ((section14State section14Catalog 8).plans.drop 7).take 1, section14PlanValid section14Catalog (section14State section14Catalog 8) p := by sorry
