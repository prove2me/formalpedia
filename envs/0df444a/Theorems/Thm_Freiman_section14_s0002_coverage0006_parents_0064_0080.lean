-- Prove2me | Theorems.Thm_Freiman_section14_s0002_coverage0006_parents_0064_0080
-- name    : Freiman.section14_s0002_coverage0006_parents_0064_0080
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T04:52:09.891793+00:00
-- url     : https://prove2.me/theorems/529880bc-5e6a-417d-a4f7-d4f84e092b3a
-- title:
--   Freiman.section14_s0002_coverage0006_parents_0064_0080
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 2).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 64).take 16, section14Recorded section14Catalog 2 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 2 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_coverage0006_parents_0064_0080 : ∀ pl ∈ ((section14State section14Catalog 2).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 64).take 16, section14Recorded section14Catalog 2 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 2 b.branch gs.1 j := by sorry
