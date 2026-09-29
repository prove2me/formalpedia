-- Prove2me | Theorems.Thm_Freiman_section14_s0007_coverage0005_parents_0012_0016
-- name    : Freiman.section14_s0007_coverage0005_parents_0012_0016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T11:14:29.824203+00:00
-- url     : https://prove2.me/theorems/d3f7c0dc-c17f-4bf4-8344-ed88ab24c360
-- title:
--   Freiman.section14_s0007_coverage0005_parents_0012_0016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 7).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 7)).drop 12).take 4, section14Recorded section14Catalog 7 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 7 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_coverage0005_parents_0012_0016 : ∀ pl ∈ ((section14State section14Catalog 7).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 7)).drop 12).take 4, section14Recorded section14Catalog 7 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 7 b.branch gs.1 j := by sorry
