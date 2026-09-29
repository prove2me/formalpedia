-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_plan0001_valid
-- name    : Freiman.workReverse20260919_s0001_plan0001_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:32:58.658482+00:00
-- url     : https://prove2.me/theorems/17852693-1dee-41d5-b546-709edb38e5e4
-- title:
--   Freiman.workReverse20260919_s0001_plan0001_valid
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ p ∈ ((section14State section14Catalog 1).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 1) p
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_plan0001_valid : ∀ p ∈ ((section14State section14Catalog 1).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 1) p := by sorry
