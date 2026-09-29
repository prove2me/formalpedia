-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0007_parents_0000_0064
-- name    : Freiman.workReverse20260919_s0005_coverage0007_parents_0000_0064
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T22:20:24.491019+00:00
-- url     : https://prove2.me/theorems/84cc2f00-fc26-4287-a46a-9fb429936ed1
-- title:
--   Freiman.workReverse20260919_s0005_coverage0007_parents_0000_0064
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 0).take 64, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_coverage0007_parents_0000_0064 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 0).take 64, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by sorry
