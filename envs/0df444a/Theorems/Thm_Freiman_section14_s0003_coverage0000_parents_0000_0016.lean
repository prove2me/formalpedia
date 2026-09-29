-- Prove2me | Theorems.Thm_Freiman_section14_s0003_coverage0000_parents_0000_0016
-- name    : Freiman.section14_s0003_coverage0000_parents_0000_0016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T11:46:32.397036+00:00
-- url     : https://prove2.me/theorems/9f310c62-69b8-4da4-a912-6d46e23fd40d
-- title:
--   Freiman.section14_s0003_coverage0000_parents_0000_0016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 3).plans.drop 0).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 3)).drop 0).take 16, section14Recorded section14Catalog 3 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_coverage0000_parents_0000_0016 : ∀ pl ∈ ((section14State section14Catalog 3).plans.drop 0).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 3)).drop 0).take 16, section14Recorded section14Catalog 3 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 b.branch gs.1 j := by sorry
