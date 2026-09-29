-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0005_parents_0168_0176
-- name    : Freiman.workReverse20260919_s0005_coverage0005_parents_0168_0176
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T05:08:21.71887+00:00
-- url     : https://prove2.me/theorems/6008e19a-dd3b-420a-a109-f72139af0a86
-- title:
--   Freiman.workReverse20260919_s0005_coverage0005_parents_0168_0176
-- statement:
--   The proved disjoint list slices concatenate to the entire original list. Applying each slice theorem to its part supplies the exact original quantified assertion.
--
--   ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 168).take 8, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_coverage0005_parents_0168_0176 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 168).take 8, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by sorry
