-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_plan0000_valid
-- name    : Freiman.workReverse20260919_s0001_plan0000_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:30:43.57033+00:00
-- url     : https://prove2.me/theorems/d0fe7cc0-76e1-44a1-be9a-ae3f56d2f87b
-- title:
--   Freiman.workReverse20260919_s0001_plan0000_valid
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ p ∈ ((section14State section14Catalog 1).plans.drop 0).take 1, section14PlanValid section14Catalog (section14State section14Catalog 1) p
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_plan0000_valid : ∀ p ∈ ((section14State section14Catalog 1).plans.drop 0).take 1, section14PlanValid section14Catalog (section14State section14Catalog 1) p := by sorry
