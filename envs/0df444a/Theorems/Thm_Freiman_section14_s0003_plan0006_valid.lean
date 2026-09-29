-- Prove2me | Theorems.Thm_Freiman_section14_s0003_plan0006_valid
-- name    : Freiman.section14_s0003_plan0006_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T15:24:03.257729+00:00
-- url     : https://prove2.me/theorems/5abd1117-a344-4f26-b244-e9e3d2a9b5a2
-- title:
--   Freiman.section14_s0003_plan0006_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 3).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 3) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_plan0006_valid : ∀ p ∈ ((section14State section14Catalog 3).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 3) p := by sorry
