-- Prove2me | Theorems.Thm_Freiman_section14_s0013_coverage0001_parents_0240_0256
-- name    : Freiman.section14_s0013_coverage0001_parents_0240_0256
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T10:02:31.996159+00:00
-- url     : https://prove2.me/theorems/df50b04a-c71f-429c-88d6-05aa2f4b2c17
-- title:
--   Freiman.section14_s0013_coverage0001_parents_0240_0256
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 240).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_coverage0001_parents_0240_0256 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 240).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by sorry
