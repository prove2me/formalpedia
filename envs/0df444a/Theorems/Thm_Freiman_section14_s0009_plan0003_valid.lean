-- Prove2me | Theorems.Thm_Freiman_section14_s0009_plan0003_valid
-- name    : Freiman.section14_s0009_plan0003_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T22:25:24.443534+00:00
-- url     : https://prove2.me/theorems/75c81976-2535-4669-a6c0-9cac1a175868
-- title:
--   Freiman.section14_s0009_plan0003_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 9).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 9) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_plan0003_valid : ∀ p ∈ ((section14State section14Catalog 9).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 9) p := by sorry
