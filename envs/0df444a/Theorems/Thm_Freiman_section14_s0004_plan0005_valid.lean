-- Prove2me | Theorems.Thm_Freiman_section14_s0004_plan0005_valid
-- name    : Freiman.section14_s0004_plan0005_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T03:21:16.076015+00:00
-- url     : https://prove2.me/theorems/c7eddbe5-fdeb-484b-8cb6-f90ed769f6b8
-- title:
--   Freiman.section14_s0004_plan0005_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 4).plans.drop 5).take 1, section14PlanValid section14Catalog (section14State section14Catalog 4) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_plan0005_valid : ∀ p ∈ ((section14State section14Catalog 4).plans.drop 5).take 1, section14PlanValid section14Catalog (section14State section14Catalog 4) p := by sorry
