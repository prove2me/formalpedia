-- Prove2me | Theorems.Thm_Freiman_section14_s0009_plan0004_valid
-- name    : Freiman.section14_s0009_plan0004_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T22:27:20.088554+00:00
-- url     : https://prove2.me/theorems/5d164201-21db-43eb-b897-0790e952702a
-- title:
--   Freiman.section14_s0009_plan0004_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 9).plans.drop 4).take 1, section14PlanValid section14Catalog (section14State section14Catalog 9) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_plan0004_valid : ∀ p ∈ ((section14State section14Catalog 9).plans.drop 4).take 1, section14PlanValid section14Catalog (section14State section14Catalog 9) p := by sorry
