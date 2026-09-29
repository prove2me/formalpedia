-- Prove2me | Theorems.Thm_Freiman_section14_s0002_coverage0000_parents_0096_0112
-- name    : Freiman.section14_s0002_coverage0000_parents_0096_0112
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:37:55.314992+00:00
-- url     : https://prove2.me/theorems/c9b42839-b2ca-45d4-b3d7-4e882466ece4
-- title:
--   Freiman.section14_s0002_coverage0000_parents_0096_0112
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 2).plans.drop 0).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 96).take 16, section14Recorded section14Catalog 2 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 2 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_coverage0000_parents_0096_0112 : ∀ pl ∈ ((section14State section14Catalog 2).plans.drop 0).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 96).take 16, section14Recorded section14Catalog 2 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 2 b.branch gs.1 j := by sorry
