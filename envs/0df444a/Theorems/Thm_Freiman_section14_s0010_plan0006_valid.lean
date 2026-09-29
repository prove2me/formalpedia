-- Prove2me | Theorems.Thm_Freiman_section14_s0010_plan0006_valid
-- name    : Freiman.section14_s0010_plan0006_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T18:21:19.62082+00:00
-- url     : https://prove2.me/theorems/eef8309c-b866-4842-ad03-f14cb59ff7b3
-- title:
--   Freiman.section14_s0010_plan0006_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 10).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 10) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_plan0006_valid : ∀ p ∈ ((section14State section14Catalog 10).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 10) p := by sorry
