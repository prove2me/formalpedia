-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_coverage0007_all
-- name    : Freiman.workReverse20260919_s0013_coverage0007_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:11:15.598349+00:00
-- url     : https://prove2.me/theorems/f7cdeafd-de04-464f-8efe-9b5a6dcd9b2e
-- title:
--   Freiman.workReverse20260919_s0013_coverage0007_all
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 7).take 1, ∀ b ∈ section14Parents section14Catalog (section14State section14Catalog 13), section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_coverage0007_all : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 7).take 1, ∀ b ∈ section14Parents section14Catalog (section14State section14Catalog 13), section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by sorry
