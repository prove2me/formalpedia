-- Prove2me | Theorems.Thm_Freiman_section14_s0007_coverage0002_parents_0000_0016
-- name    : Freiman.section14_s0007_coverage0002_parents_0000_0016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:49:05.061565+00:00
-- url     : https://prove2.me/theorems/af844d0e-e913-4953-b3a3-50fb63727622
-- title:
--   Freiman.section14_s0007_coverage0002_parents_0000_0016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 7).plans.drop 2).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 7)).drop 0).take 16, section14Recorded section14Catalog 7 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 7 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_coverage0002_parents_0000_0016 : ∀ pl ∈ ((section14State section14Catalog 7).plans.drop 2).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 7)).drop 0).take 16, section14Recorded section14Catalog 7 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 7 b.branch gs.1 j := by sorry
