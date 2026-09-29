-- Prove2me | Theorems.Thm_Freiman_section14_s0002_coverage0001_parents_0208_0224
-- name    : Freiman.section14_s0002_coverage0001_parents_0208_0224
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:53:44.782989+00:00
-- url     : https://prove2.me/theorems/acf97a02-07cc-447e-86b7-c5b42b7ae60b
-- title:
--   Freiman.section14_s0002_coverage0001_parents_0208_0224
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ pl ∈ ((section14State section14Catalog 2).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 208).take 16, section14Recorded section14Catalog 2 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 2 b.branch gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_coverage0001_parents_0208_0224 : ∀ pl ∈ ((section14State section14Catalog 2).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 208).take 16, section14Recorded section14Catalog 2 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 2 b.branch gs.1 j := by sorry
