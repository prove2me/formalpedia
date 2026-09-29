-- Prove2me | Theorems.Thm_Freiman_section14_s0012_plan0006_valid
-- name    : Freiman.section14_s0012_plan0006_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T05:54:49.952103+00:00
-- url     : https://prove2.me/theorems/462a389e-1964-4191-9899-8621efee95ec
-- title:
--   Freiman.section14_s0012_plan0006_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 12).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 12) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_plan0006_valid : ∀ p ∈ ((section14State section14Catalog 12).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 12) p := by sorry
