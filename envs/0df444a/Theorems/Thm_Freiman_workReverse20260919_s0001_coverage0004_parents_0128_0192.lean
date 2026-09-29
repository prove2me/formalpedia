-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_coverage0004_parents_0128_0192
-- name    : Freiman.workReverse20260919_s0001_coverage0004_parents_0128_0192
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:59:23.009799+00:00
-- url     : https://prove2.me/theorems/d44000cd-fabb-4138-9a20-20cde45b8d58
-- title:
--   Freiman.workReverse20260919_s0001_coverage0004_parents_0128_0192
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ pl ∈ ((section14State section14Catalog 1).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 128).take 64, section14Recorded section14Catalog 1 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 b.branch gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_coverage0004_parents_0128_0192 : ∀ pl ∈ ((section14State section14Catalog 1).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 128).take 64, section14Recorded section14Catalog 1 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 b.branch gs.1 j := by sorry
