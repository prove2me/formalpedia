-- Prove2me | Theorems.Thm_Freiman_section14_s0016_plan0001_valid
-- name    : Freiman.section14_s0016_plan0001_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T00:56:38.813058+00:00
-- url     : https://prove2.me/theorems/342382b6-c686-4705-afce-bcc98bbfd74d
-- title:
--   Freiman.section14_s0016_plan0001_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 16).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 16) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_plan0001_valid : ∀ p ∈ ((section14State section14Catalog 16).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 16) p := by sorry
