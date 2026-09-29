-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_coverage0005_parents_0168_0176
-- name    : Freiman.workReverse20260919_s0006_coverage0005_parents_0168_0176
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T04:59:34.426981+00:00
-- url     : https://prove2.me/theorems/83ff5b32-f9a9-44cb-843e-2244af27b611
-- title:
--   Freiman.workReverse20260919_s0006_coverage0005_parents_0168_0176
-- statement:
--   The proved disjoint list slices concatenate to the entire original list. Applying each slice theorem to its part supplies the exact original quantified assertion.
--
--   ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 168).take 8, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_coverage0005_parents_0168_0176 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 168).take 8, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by sorry
