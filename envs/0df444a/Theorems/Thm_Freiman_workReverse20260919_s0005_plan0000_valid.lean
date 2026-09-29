-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_plan0000_valid
-- name    : Freiman.workReverse20260919_s0005_plan0000_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T20:15:57.16498+00:00
-- url     : https://prove2.me/theorems/3604f13c-5a8f-435b-8cea-fa2cee53dfff
-- title:
--   Freiman.workReverse20260919_s0005_plan0000_valid
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ p ∈ ((section14State section14Catalog 5).plans.drop 0).take 1, section14PlanValid section14Catalog (section14State section14Catalog 5) p
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_plan0000_valid : ∀ p ∈ ((section14State section14Catalog 5).plans.drop 0).take 1, section14PlanValid section14Catalog (section14State section14Catalog 5) p := by sorry
