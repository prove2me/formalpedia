-- Prove2me | Theorems.Thm_Freiman_section14_s0014_coverage0002_parents_0080_0096
-- name    : Freiman.section14_s0014_coverage0002_parents_0080_0096
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T23:42:52.845977+00:00
-- url     : https://prove2.me/theorems/fd9c3ea9-b00b-4e97-a2dc-6cfe8886fade
-- title:
--   Freiman.section14_s0014_coverage0002_parents_0080_0096
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 14).plans.drop 2).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 14)).drop 80).take 16, section14Recorded section14Catalog 14 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 14 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_coverage0002_parents_0080_0096 : ∀ pl ∈ ((section14State section14Catalog 14).plans.drop 2).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 14)).drop 80).take 16, section14Recorded section14Catalog 14 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 14 b.branch gs.1 j := by sorry
