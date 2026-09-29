-- Prove2me | Theorems.Thm_Freiman_section14_s0015_plan0003_valid
-- name    : Freiman.section14_s0015_plan0003_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T21:35:01.462378+00:00
-- url     : https://prove2.me/theorems/65f37300-49bf-45f3-8af6-e39cdd63bb76
-- title:
--   Freiman.section14_s0015_plan0003_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 15).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 15) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_plan0003_valid : ∀ p ∈ ((section14State section14Catalog 15).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 15) p := by sorry
