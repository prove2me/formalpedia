-- Prove2me | Theorems.Thm_Freiman_section14_s0008_plan0005_valid
-- name    : Freiman.section14_s0008_plan0005_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:22:21.132426+00:00
-- url     : https://prove2.me/theorems/82fb64c9-99d7-4ce9-8a0c-ff3e7a1fe999
-- title:
--   Freiman.section14_s0008_plan0005_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 8).plans.drop 5).take 1, section14PlanValid section14Catalog (section14State section14Catalog 8) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_plan0005_valid : ∀ p ∈ ((section14State section14Catalog 8).plans.drop 5).take 1, section14PlanValid section14Catalog (section14State section14Catalog 8) p := by sorry
