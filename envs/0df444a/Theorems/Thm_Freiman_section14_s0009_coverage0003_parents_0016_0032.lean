-- Prove2me | Theorems.Thm_Freiman_section14_s0009_coverage0003_parents_0016_0032
-- name    : Freiman.section14_s0009_coverage0003_parents_0016_0032
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T19:01:31.464656+00:00
-- url     : https://prove2.me/theorems/7f4f32d2-2182-4884-abd5-51a9d93eac93
-- title:
--   Freiman.section14_s0009_coverage0003_parents_0016_0032
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 9).plans.drop 3).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 9)).drop 16).take 16, section14Recorded section14Catalog 9 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 9 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_coverage0003_parents_0016_0032 : ∀ pl ∈ ((section14State section14Catalog 9).plans.drop 3).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 9)).drop 16).take 16, section14Recorded section14Catalog 9 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 9 b.branch gs.1 j := by sorry
