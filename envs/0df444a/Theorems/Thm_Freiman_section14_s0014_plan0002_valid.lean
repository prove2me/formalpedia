-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plan0002_valid
-- name    : Freiman.section14_s0014_plan0002_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:04:48.965247+00:00
-- url     : https://prove2.me/theorems/1c2351d6-05d9-4ae9-a3d2-27f72a08ace9
-- title:
--   Freiman.section14_s0014_plan0002_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 14).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 14) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plan0002_valid : ∀ p ∈ ((section14State section14Catalog 14).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 14) p := by sorry
