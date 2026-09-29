-- Prove2me | Theorems.Thm_Freiman_section14_s0004_plan0006_valid
-- name    : Freiman.section14_s0004_plan0006_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T03:22:42.4084+00:00
-- url     : https://prove2.me/theorems/91f84d78-b0c7-43b5-a4c4-d49bc6bc9c99
-- title:
--   Freiman.section14_s0004_plan0006_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 4).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 4) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_plan0006_valid : ∀ p ∈ ((section14State section14Catalog 4).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 4) p := by sorry
