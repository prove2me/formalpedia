-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_coverage0004_parents_0192_0256
-- name    : Freiman.workReverse20260919_s0006_coverage0004_parents_0192_0256
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:07:31.606245+00:00
-- url     : https://prove2.me/theorems/267bb279-90b1-413d-ac3b-220d7cea751c
-- title:
--   Freiman.workReverse20260919_s0006_coverage0004_parents_0192_0256
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 192).take 64, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_coverage0004_parents_0192_0256 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 192).take 64, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by sorry
