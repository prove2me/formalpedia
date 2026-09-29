-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0005_parents_0128_0160
-- name    : Freiman.workReverse20260919_s0005_coverage0005_parents_0128_0160
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T22:07:36.38764+00:00
-- url     : https://prove2.me/theorems/a9bfcb96-dcc0-489b-837d-ae964c5dcaa0
-- title:
--   Freiman.workReverse20260919_s0005_coverage0005_parents_0128_0160
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 128).take 32, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_coverage0005_parents_0128_0160 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 128).take 32, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by sorry
