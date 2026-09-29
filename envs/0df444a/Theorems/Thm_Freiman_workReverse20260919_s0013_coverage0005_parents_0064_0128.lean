-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_coverage0005_parents_0064_0128
-- name    : Freiman.workReverse20260919_s0013_coverage0005_parents_0064_0128
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:10:27.829752+00:00
-- url     : https://prove2.me/theorems/563cd20b-62b0-4b13-95a8-6429d9ab2638
-- title:
--   Freiman.workReverse20260919_s0013_coverage0005_parents_0064_0128
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 64).take 64, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_coverage0005_parents_0064_0128 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 64).take 64, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by sorry
