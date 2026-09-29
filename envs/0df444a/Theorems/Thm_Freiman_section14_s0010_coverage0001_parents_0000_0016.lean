-- Prove2me | Theorems.Thm_Freiman_section14_s0010_coverage0001_parents_0000_0016
-- name    : Freiman.section14_s0010_coverage0001_parents_0000_0016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T15:46:04.307951+00:00
-- url     : https://prove2.me/theorems/fd6212c2-67cc-4b65-a84e-2961ef19f0c8
-- title:
--   Freiman.section14_s0010_coverage0001_parents_0000_0016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 10).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 10)).drop 0).take 16, section14Recorded section14Catalog 10 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 10 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_coverage0001_parents_0000_0016 : ∀ pl ∈ ((section14State section14Catalog 10).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 10)).drop 0).take 16, section14Recorded section14Catalog 10 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 10 b.branch gs.1 j := by sorry
