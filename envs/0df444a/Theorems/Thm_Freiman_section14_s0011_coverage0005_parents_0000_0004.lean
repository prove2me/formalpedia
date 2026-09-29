-- Prove2me | Theorems.Thm_Freiman_section14_s0011_coverage0005_parents_0000_0004
-- name    : Freiman.section14_s0011_coverage0005_parents_0000_0004
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T12:06:11.378277+00:00
-- url     : https://prove2.me/theorems/da1c69f2-f1d8-4dee-8e3b-a627d6f6240e
-- title:
--   Freiman.section14_s0011_coverage0005_parents_0000_0004
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 11).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 11)).drop 0).take 4, section14Recorded section14Catalog 11 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 11 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_coverage0005_parents_0000_0004 : ∀ pl ∈ ((section14State section14Catalog 11).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 11)).drop 0).take 4, section14Recorded section14Catalog 11 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 11 b.branch gs.1 j := by sorry
