-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_coverage0004_parents_0168_0176_timeout_d01ff0ff
-- name    : Freiman.workReverse20260919_s0001_coverage0004_parents_0168_0176_timeout_d01ff0ff
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T22:52:53.383916+00:00
-- url     : https://prove2.me/theorems/feae0740-53d5-4bbf-b335-034946f55c77
-- title:
--   Freiman.workReverse20260919_s0001_coverage0004_parents_0168_0176_timeout_d01ff0ff
-- statement:
--   Exact original coverage generator on a strict eight-parent slice of the server-timed-out interval; unchanged original catalogue and coverage predicate.
--
--   ∀ pl ∈ ((section14State section14Catalog 1).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 168).take 8, section14Recorded section14Catalog 1 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 b.branch gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_coverage0004_parents_0168_0176_timeout_d01ff0ff : ∀ pl ∈ ((section14State section14Catalog 1).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 168).take 8, section14Recorded section14Catalog 1 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 b.branch gs.1 j := by sorry
