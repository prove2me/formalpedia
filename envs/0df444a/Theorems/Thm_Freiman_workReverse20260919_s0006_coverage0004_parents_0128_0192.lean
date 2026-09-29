-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_coverage0004_parents_0128_0192
-- name    : Freiman.workReverse20260919_s0006_coverage0004_parents_0128_0192
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:36:12.525493+00:00
-- url     : https://prove2.me/theorems/0cd5c9d5-15e2-4516-8c02-b5e2d3a0289c
-- title:
--   Freiman.workReverse20260919_s0006_coverage0004_parents_0128_0192
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 128).take 64, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_coverage0004_parents_0128_0192 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 128).take 64, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by sorry
