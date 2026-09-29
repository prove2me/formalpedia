-- Prove2me | Theorems.Thm_Freiman_section14_s0002_coverage0007_parents_0128_0144
-- name    : Freiman.section14_s0002_coverage0007_parents_0128_0144
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T05:42:35.894249+00:00
-- url     : https://prove2.me/theorems/de09c976-eec8-4c4d-b3a8-2bbf1e860f23
-- title:
--   Freiman.section14_s0002_coverage0007_parents_0128_0144
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 2).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 128).take 16, section14Recorded section14Catalog 2 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 2 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_coverage0007_parents_0128_0144 : ∀ pl ∈ ((section14State section14Catalog 2).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 128).take 16, section14Recorded section14Catalog 2 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 2 b.branch gs.1 j := by sorry
