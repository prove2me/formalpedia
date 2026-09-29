-- Prove2me | Theorems.Thm_Freiman_section14_s0004_plan0007_valid
-- name    : Freiman.section14_s0004_plan0007_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T03:24:00.145006+00:00
-- url     : https://prove2.me/theorems/f0313f5a-45e2-4ccd-8207-872ff5e08047
-- title:
--   Freiman.section14_s0004_plan0007_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 4).plans.drop 7).take 1, section14PlanValid section14Catalog (section14State section14Catalog 4) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_plan0007_valid : ∀ p ∈ ((section14State section14Catalog 4).plans.drop 7).take 1, section14PlanValid section14Catalog (section14State section14Catalog 4) p := by sorry
