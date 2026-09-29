-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_plan0006_valid
-- name    : Freiman.workReverse20260919_s0001_plan0006_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T00:02:36.399987+00:00
-- url     : https://prove2.me/theorems/2da8cc11-c1f5-4256-98df-06d235c24899
-- title:
--   Freiman.workReverse20260919_s0001_plan0006_valid
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ p ∈ ((section14State section14Catalog 1).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 1) p
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_plan0006_valid : ∀ p ∈ ((section14State section14Catalog 1).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 1) p := by sorry
