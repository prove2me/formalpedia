-- Prove2me | Theorems.Thm_Freiman_section14_s0004_coverage0000_parents_0000_0016
-- name    : Freiman.section14_s0004_coverage0000_parents_0000_0016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T01:28:03.537823+00:00
-- url     : https://prove2.me/theorems/118a95c5-2d7a-42a4-8386-e6c16d1a2a78
-- title:
--   Freiman.section14_s0004_coverage0000_parents_0000_0016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 4).plans.drop 0).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 4)).drop 0).take 16, section14Recorded section14Catalog 4 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 4 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_coverage0000_parents_0000_0016 : ∀ pl ∈ ((section14State section14Catalog 4).plans.drop 0).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 4)).drop 0).take 16, section14Recorded section14Catalog 4 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 4 b.branch gs.1 j := by sorry
