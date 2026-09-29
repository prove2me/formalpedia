-- Prove2me | Theorems.Thm_Freiman_section14_s0014_coverage0006_parents_0096_0112
-- name    : Freiman.section14_s0014_coverage0006_parents_0096_0112
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T00:54:02.365527+00:00
-- url     : https://prove2.me/theorems/9c1c4621-3e1e-42b7-bc94-f2dc37819316
-- title:
--   Freiman.section14_s0014_coverage0006_parents_0096_0112
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 14).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 14)).drop 96).take 16, section14Recorded section14Catalog 14 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 14 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_coverage0006_parents_0096_0112 : ∀ pl ∈ ((section14State section14Catalog 14).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 14)).drop 96).take 16, section14Recorded section14Catalog 14 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 14 b.branch gs.1 j := by sorry
