-- Prove2me | Theorems.Thm_Freiman_section14_s0016_plan0002_valid
-- name    : Freiman.section14_s0016_plan0002_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T00:54:08.121321+00:00
-- url     : https://prove2.me/theorems/f479d54e-fdbb-4895-89e8-8592f875b6e4
-- title:
--   Freiman.section14_s0016_plan0002_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 16).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 16) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_plan0002_valid : ∀ p ∈ ((section14State section14Catalog 16).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 16) p := by sorry
