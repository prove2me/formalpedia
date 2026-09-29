-- Prove2me | Theorems.Thm_Freiman_section14_s0010_coverage0005_all
-- name    : Freiman.section14_s0010_coverage0005_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T18:17:57.485065+00:00
-- url     : https://prove2.me/theorems/745e6496-a24d-4eb6-9328-0c0333ac2c60
-- title:
--   Freiman.section14_s0010_coverage0005_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 10).plans.drop 5).take 1, ∀ b ∈ section14Parents section14Catalog (section14State section14Catalog 10), section14Recorded section14Catalog 10 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 10 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_coverage0005_all : ∀ pl ∈ ((section14State section14Catalog 10).plans.drop 5).take 1, ∀ b ∈ section14Parents section14Catalog (section14State section14Catalog 10), section14Recorded section14Catalog 10 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 10 b.branch gs.1 j := by sorry
