-- Prove2me | Theorems.Thm_Freiman_section14_s0016_coverage0006_parents_0000_0016
-- name    : Freiman.section14_s0016_coverage0006_parents_0000_0016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T22:24:14.327893+00:00
-- url     : https://prove2.me/theorems/3e748cfb-5936-45b1-8447-a4295f2431f7
-- title:
--   Freiman.section14_s0016_coverage0006_parents_0000_0016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 16).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 16)).drop 0).take 16, section14Recorded section14Catalog 16 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 16 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_coverage0006_parents_0000_0016 : ∀ pl ∈ ((section14State section14Catalog 16).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 16)).drop 0).take 16, section14Recorded section14Catalog 16 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 16 b.branch gs.1 j := by sorry
