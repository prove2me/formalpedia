-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_coverage0005_parents_0176_0192
-- name    : Freiman.workReverse20260919_s0001_coverage0005_parents_0176_0192
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T00:02:33.522988+00:00
-- url     : https://prove2.me/theorems/416bd3c6-12ea-4fdc-97f6-5d607e31c088
-- title:
--   Freiman.workReverse20260919_s0001_coverage0005_parents_0176_0192
-- statement:
--   Explicit original catalogue records cover every required nonautomatic branch. Every automatic branch is checked directly. The stated parent and plan slices are exhausted without omission.
--
--   ∀ pl ∈ ((section14State section14Catalog 1).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 176).take 16, section14Recorded section14Catalog 1 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 b.branch gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_coverage0005_parents_0176_0192 : ∀ pl ∈ ((section14State section14Catalog 1).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 176).take 16, section14Recorded section14Catalog 1 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 b.branch gs.1 j := by sorry
