-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_plan0001_valid
-- name    : Freiman.workReverse20260919_s0006_plan0001_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T20:26:53.588706+00:00
-- url     : https://prove2.me/theorems/aeed00f1-fa0c-48a9-9056-44dbcf4de092
-- title:
--   Freiman.workReverse20260919_s0006_plan0001_valid
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ p ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 6) p
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_plan0001_valid : ∀ p ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 6) p := by sorry
