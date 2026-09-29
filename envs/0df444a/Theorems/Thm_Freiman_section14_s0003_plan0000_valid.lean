-- Prove2me | Theorems.Thm_Freiman_section14_s0003_plan0000_valid
-- name    : Freiman.section14_s0003_plan0000_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T15:14:11.509538+00:00
-- url     : https://prove2.me/theorems/654e995a-21aa-4db8-a901-1f7b359755e9
-- title:
--   Freiman.section14_s0003_plan0000_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 3).plans.drop 0).take 1, section14PlanValid section14Catalog (section14State section14Catalog 3) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_plan0000_valid : ∀ p ∈ ((section14State section14Catalog 3).plans.drop 0).take 1, section14PlanValid section14Catalog (section14State section14Catalog 3) p := by sorry
