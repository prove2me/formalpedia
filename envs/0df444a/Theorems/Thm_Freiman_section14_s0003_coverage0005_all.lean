-- Prove2me | Theorems.Thm_Freiman_section14_s0003_coverage0005_all
-- name    : Freiman.section14_s0003_coverage0005_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T15:19:38.289567+00:00
-- url     : https://prove2.me/theorems/f63e292d-43ac-4833-b52b-e764db0a641d
-- title:
--   Freiman.section14_s0003_coverage0005_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 3).plans.drop 5).take 1, ∀ b ∈ section14Parents section14Catalog (section14State section14Catalog 3), section14Recorded section14Catalog 3 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_coverage0005_all : ∀ pl ∈ ((section14State section14Catalog 3).plans.drop 5).take 1, ∀ b ∈ section14Parents section14Catalog (section14State section14Catalog 3), section14Recorded section14Catalog 3 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 b.branch gs.1 j := by sorry
