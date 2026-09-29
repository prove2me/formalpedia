-- Prove2me | Theorems.Thm_Freiman_section14_s0009_plan0002_valid
-- name    : Freiman.section14_s0009_plan0002_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T22:17:04.013707+00:00
-- url     : https://prove2.me/theorems/8ab4aff0-ec34-4d03-98db-96d51c2d7773
-- title:
--   Freiman.section14_s0009_plan0002_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 9).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 9) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_plan0002_valid : ∀ p ∈ ((section14State section14Catalog 9).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 9) p := by sorry
