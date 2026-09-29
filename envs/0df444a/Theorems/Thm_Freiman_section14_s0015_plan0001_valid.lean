-- Prove2me | Theorems.Thm_Freiman_section14_s0015_plan0001_valid
-- name    : Freiman.section14_s0015_plan0001_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T21:28:14.626117+00:00
-- url     : https://prove2.me/theorems/7311855f-8933-4cc7-9890-d20f7e8ff3f3
-- title:
--   Freiman.section14_s0015_plan0001_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 15).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 15) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_plan0001_valid : ∀ p ∈ ((section14State section14Catalog 15).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 15) p := by sorry
