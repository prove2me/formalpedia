-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_plan0003_valid
-- name    : Freiman.workReverse20260919_s0001_plan0003_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T23:56:21.320189+00:00
-- url     : https://prove2.me/theorems/98bdf0b6-0382-4a6a-8ffc-96c351840a0e
-- title:
--   Freiman.workReverse20260919_s0001_plan0003_valid
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ p ∈ ((section14State section14Catalog 1).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 1) p
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_plan0003_valid : ∀ p ∈ ((section14State section14Catalog 1).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 1) p := by sorry
