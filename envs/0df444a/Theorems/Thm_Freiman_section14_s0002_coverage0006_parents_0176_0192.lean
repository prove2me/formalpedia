-- Prove2me | Theorems.Thm_Freiman_section14_s0002_coverage0006_parents_0176_0192
-- name    : Freiman.section14_s0002_coverage0006_parents_0176_0192
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T05:06:25.037998+00:00
-- url     : https://prove2.me/theorems/369006ef-73c1-4649-aa65-4c66768b9d9f
-- title:
--   Freiman.section14_s0002_coverage0006_parents_0176_0192
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 2).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 176).take 16, section14Recorded section14Catalog 2 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 2 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_coverage0006_parents_0176_0192 : ∀ pl ∈ ((section14State section14Catalog 2).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 176).take 16, section14Recorded section14Catalog 2 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 2 b.branch gs.1 j := by sorry
