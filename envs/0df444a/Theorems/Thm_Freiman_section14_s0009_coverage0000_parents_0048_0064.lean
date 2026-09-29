-- Prove2me | Theorems.Thm_Freiman_section14_s0009_coverage0000_parents_0048_0064
-- name    : Freiman.section14_s0009_coverage0000_parents_0048_0064
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T18:44:14.323682+00:00
-- url     : https://prove2.me/theorems/eea4e3d4-2d85-4b80-ba4a-1dfd48427a3a
-- title:
--   Freiman.section14_s0009_coverage0000_parents_0048_0064
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 9).plans.drop 0).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 9)).drop 48).take 16, section14Recorded section14Catalog 9 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 9 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_coverage0000_parents_0048_0064 : ∀ pl ∈ ((section14State section14Catalog 9).plans.drop 0).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 9)).drop 48).take 16, section14Recorded section14Catalog 9 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 9 b.branch gs.1 j := by sorry
