-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plans_all
-- name    : Freiman.section14_s0014_plans_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:17:45.218417+00:00
-- url     : https://prove2.me/theorems/4ab931a9-6b2a-4d46-889a-04c79dd6cfd7
-- title:
--   Freiman.section14_s0014_plans_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ (section14State section14Catalog 14).plans, section14PlanValid section14Catalog (section14State section14Catalog 14) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plans_all : ∀ p ∈ (section14State section14Catalog 14).plans, section14PlanValid section14Catalog (section14State section14Catalog 14) p := by sorry
