-- Prove2me | Theorems.Thm_Freiman_section14_s0012_coverage0000_all
-- name    : Freiman.section14_s0012_coverage0000_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T05:43:55.11897+00:00
-- url     : https://prove2.me/theorems/99e394f9-b444-4d5a-9efc-433965a16cda
-- title:
--   Freiman.section14_s0012_coverage0000_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 12).plans.drop 0).take 1, ∀ b ∈ section14Parents section14Catalog (section14State section14Catalog 12), section14Recorded section14Catalog 12 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 12 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_coverage0000_all : ∀ pl ∈ ((section14State section14Catalog 12).plans.drop 0).take 1, ∀ b ∈ section14Parents section14Catalog (section14State section14Catalog 12), section14Recorded section14Catalog 12 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 12 b.branch gs.1 j := by sorry
