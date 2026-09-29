-- Prove2me | Theorems.Thm_Freiman_section14_s0011_coverage0005_parents_0002_0003
-- name    : Freiman.section14_s0011_coverage0005_parents_0002_0003
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T15:55:27.946535+00:00
-- url     : https://prove2.me/theorems/5b8bd0a7-3d1c-41ca-880f-a3bcdbf4dd2f
-- title:
--   Freiman.section14_s0011_coverage0005_parents_0002_0003
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 11).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 11)).drop 2).take 1, section14Recorded section14Catalog 11 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 11 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_coverage0005_parents_0002_0003 : ∀ pl ∈ ((section14State section14Catalog 11).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 11)).drop 2).take 1, section14Recorded section14Catalog 11 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 11 b.branch gs.1 j := by sorry
