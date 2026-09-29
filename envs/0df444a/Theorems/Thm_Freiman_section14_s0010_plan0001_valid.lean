-- Prove2me | Theorems.Thm_Freiman_section14_s0010_plan0001_valid
-- name    : Freiman.section14_s0010_plan0001_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T18:13:48.4714+00:00
-- url     : https://prove2.me/theorems/d0c3695c-29cd-4860-afb7-459aea3b3750
-- title:
--   Freiman.section14_s0010_plan0001_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 10).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 10) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_plan0001_valid : ∀ p ∈ ((section14State section14Catalog 10).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 10) p := by sorry
