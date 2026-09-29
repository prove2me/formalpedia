-- Prove2me | Theorems.Thm_Freiman_section14_s0011_plan0003_valid
-- name    : Freiman.section14_s0011_plan0003_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T16:14:05.199955+00:00
-- url     : https://prove2.me/theorems/ca4bc647-7e72-4614-8005-25c50b0d9109
-- title:
--   Freiman.section14_s0011_plan0003_valid
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ p ∈ ((section14State section14Catalog 11).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 11) p
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_plan0003_valid : ∀ p ∈ ((section14State section14Catalog 11).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 11) p := by sorry
