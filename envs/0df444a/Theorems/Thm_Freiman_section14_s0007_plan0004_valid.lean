-- Prove2me | Theorems.Thm_Freiman_section14_s0007_plan0004_valid
-- name    : Freiman.section14_s0007_plan0004_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T11:29:09.916456+00:00
-- url     : https://prove2.me/theorems/82ca0528-1a61-42f1-ad76-5b34735c147b
-- title:
--   Freiman.section14_s0007_plan0004_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 7).plans.drop 4).take 1, section14PlanValid section14Catalog (section14State section14Catalog 7) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_plan0004_valid : ∀ p ∈ ((section14State section14Catalog 7).plans.drop 4).take 1, section14PlanValid section14Catalog (section14State section14Catalog 7) p := by sorry
