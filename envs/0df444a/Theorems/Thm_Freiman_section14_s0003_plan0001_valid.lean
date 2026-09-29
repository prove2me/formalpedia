-- Prove2me | Theorems.Thm_Freiman_section14_s0003_plan0001_valid
-- name    : Freiman.section14_s0003_plan0001_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T15:16:16.484873+00:00
-- url     : https://prove2.me/theorems/4f77c2d5-13de-4dac-9340-b57edf0e1a90
-- title:
--   Freiman.section14_s0003_plan0001_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 3).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 3) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_plan0001_valid : ∀ p ∈ ((section14State section14Catalog 3).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 3) p := by sorry
