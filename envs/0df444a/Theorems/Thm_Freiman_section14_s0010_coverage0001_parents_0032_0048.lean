-- Prove2me | Theorems.Thm_Freiman_section14_s0010_coverage0001_parents_0032_0048
-- name    : Freiman.section14_s0010_coverage0001_parents_0032_0048
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T15:47:31.061385+00:00
-- url     : https://prove2.me/theorems/3af8f3a4-6b43-4089-ae6b-0751b0166c38
-- title:
--   Freiman.section14_s0010_coverage0001_parents_0032_0048
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 10).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 10)).drop 32).take 16, section14Recorded section14Catalog 10 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 10 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_coverage0001_parents_0032_0048 : ∀ pl ∈ ((section14State section14Catalog 10).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 10)).drop 32).take 16, section14Recorded section14Catalog 10 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 10 b.branch gs.1 j := by sorry
