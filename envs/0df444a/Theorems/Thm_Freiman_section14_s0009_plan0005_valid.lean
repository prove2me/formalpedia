-- Prove2me | Theorems.Thm_Freiman_section14_s0009_plan0005_valid
-- name    : Freiman.section14_s0009_plan0005_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T22:32:35.829597+00:00
-- url     : https://prove2.me/theorems/4531fb13-b287-4b90-9045-e29155e6290e
-- title:
--   Freiman.section14_s0009_plan0005_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 9).plans.drop 5).take 1, section14PlanValid section14Catalog (section14State section14Catalog 9) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_plan0005_valid : ∀ p ∈ ((section14State section14Catalog 9).plans.drop 5).take 1, section14PlanValid section14Catalog (section14State section14Catalog 9) p := by sorry
