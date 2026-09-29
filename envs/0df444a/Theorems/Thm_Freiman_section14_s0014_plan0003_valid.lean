-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plan0003_valid
-- name    : Freiman.section14_s0014_plan0003_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:09:25.024022+00:00
-- url     : https://prove2.me/theorems/cdcea141-69c2-4022-8508-7a4f50bd2f76
-- title:
--   Freiman.section14_s0014_plan0003_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 14).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 14) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plan0003_valid : ∀ p ∈ ((section14State section14Catalog 14).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 14) p := by sorry
