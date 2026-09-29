-- Prove2me | Theorems.Thm_Freiman_section14_s0014_coverage0004_parents_0240_0256
-- name    : Freiman.section14_s0014_coverage0004_parents_0240_0256
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T00:26:54.329171+00:00
-- url     : https://prove2.me/theorems/87bd7040-3dbf-45f8-b9a1-a4fd76ff3174
-- title:
--   Freiman.section14_s0014_coverage0004_parents_0240_0256
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 14).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 14)).drop 240).take 16, section14Recorded section14Catalog 14 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 14 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_coverage0004_parents_0240_0256 : ∀ pl ∈ ((section14State section14Catalog 14).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 14)).drop 240).take 16, section14Recorded section14Catalog 14 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 14 b.branch gs.1 j := by sorry
