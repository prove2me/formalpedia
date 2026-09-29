-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_coverage0004_parents_0176_0192
-- name    : Freiman.workReverse20260919_s0013_coverage0004_parents_0176_0192
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T10:05:05.47319+00:00
-- url     : https://prove2.me/theorems/ecad24d9-dd53-41e4-8504-e481aa925d21
-- title:
--   Freiman.workReverse20260919_s0013_coverage0004_parents_0176_0192
-- statement:
--   Explicit original catalogue records cover every required nonautomatic branch. Every automatic branch is checked directly. The stated parent and plan slices are exhausted without omission.
--
--   ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 176).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_coverage0004_parents_0176_0192 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 176).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by sorry
