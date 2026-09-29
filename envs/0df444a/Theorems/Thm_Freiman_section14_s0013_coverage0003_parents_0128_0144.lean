-- Prove2me | Theorems.Thm_Freiman_section14_s0013_coverage0003_parents_0128_0144
-- name    : Freiman.section14_s0013_coverage0003_parents_0128_0144
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T10:30:29.452249+00:00
-- url     : https://prove2.me/theorems/ab96f660-78ef-410b-aecd-9b8f2f2df05b
-- title:
--   Freiman.section14_s0013_coverage0003_parents_0128_0144
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 3).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 128).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_coverage0003_parents_0128_0144 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 3).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 128).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by sorry
