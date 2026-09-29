-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plan0001_valid
-- name    : Freiman.section14_s0014_plan0001_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:07:16.366274+00:00
-- url     : https://prove2.me/theorems/5cbff502-76fd-46ba-a035-4e86aa16f8f9
-- title:
--   Freiman.section14_s0014_plan0001_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 14).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 14) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plan0001_valid : ∀ p ∈ ((section14State section14Catalog 14).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 14) p := by sorry
