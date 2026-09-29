-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plan0004_valid
-- name    : Freiman.section14_s0014_plan0004_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:11:23.805983+00:00
-- url     : https://prove2.me/theorems/23d19b34-073f-4d7d-82ce-c92761194cb2
-- title:
--   Freiman.section14_s0014_plan0004_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 14).plans.drop 4).take 1, section14PlanValid section14Catalog (section14State section14Catalog 14) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plan0004_valid : ∀ p ∈ ((section14State section14Catalog 14).plans.drop 4).take 1, section14PlanValid section14Catalog (section14State section14Catalog 14) p := by sorry
