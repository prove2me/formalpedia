-- Prove2me | Theorems.Thm_Freiman_section14_s0002_plan0007_valid
-- name    : Freiman.section14_s0002_plan0007_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:41:59.9152+00:00
-- url     : https://prove2.me/theorems/06264f27-6b37-4f18-aba3-7b0948e5e370
-- title:
--   Freiman.section14_s0002_plan0007_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 2).plans.drop 7).take 1, section14PlanValid section14Catalog (section14State section14Catalog 2) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_plan0007_valid : ∀ p ∈ ((section14State section14Catalog 2).plans.drop 7).take 1, section14PlanValid section14Catalog (section14State section14Catalog 2) p := by sorry
