-- Prove2me | Theorems.Thm_Freiman_section14_s0014_coverage0003_parents_0064_0080
-- name    : Freiman.section14_s0014_coverage0003_parents_0064_0080
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T23:58:49.131114+00:00
-- url     : https://prove2.me/theorems/581f038c-8e13-4fcf-9683-16550518cfbd
-- title:
--   Freiman.section14_s0014_coverage0003_parents_0064_0080
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 14).plans.drop 3).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 14)).drop 64).take 16, section14Recorded section14Catalog 14 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 14 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_coverage0003_parents_0064_0080 : ∀ pl ∈ ((section14State section14Catalog 14).plans.drop 3).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 14)).drop 64).take 16, section14Recorded section14Catalog 14 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 14 b.branch gs.1 j := by sorry
