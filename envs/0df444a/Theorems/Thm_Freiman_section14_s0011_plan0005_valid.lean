-- Prove2me | Theorems.Thm_Freiman_section14_s0011_plan0005_valid
-- name    : Freiman.section14_s0011_plan0005_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T16:15:40.774638+00:00
-- url     : https://prove2.me/theorems/14552bb9-f4b0-428e-83a9-49c2cce9a040
-- title:
--   Freiman.section14_s0011_plan0005_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 11).plans.drop 5).take 1, section14PlanValid section14Catalog (section14State section14Catalog 11) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_plan0005_valid : ∀ p ∈ ((section14State section14Catalog 11).plans.drop 5).take 1, section14PlanValid section14Catalog (section14State section14Catalog 11) p := by sorry
