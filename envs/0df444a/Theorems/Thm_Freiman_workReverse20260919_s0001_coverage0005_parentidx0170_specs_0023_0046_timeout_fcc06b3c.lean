-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_coverage0005_parentidx0170_specs_0023_0046_timeout_fcc06b3c
-- name    : Freiman.workReverse20260919_s0001_coverage0005_parentidx0170_specs_0023_0046_timeout_fcc06b3c
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T23:41:09.508525+00:00
-- url     : https://prove2.me/theorems/f2cf0ee7-28c5-406a-bef6-796b2d6282e6
-- title:
--   Freiman.workReverse20260919_s0001_coverage0005_parentidx0170_specs_0023_0046_timeout_fcc06b3c
-- statement:
--   Exact original coverage specification generator restricted to the stated strict slice of parent170; all original goals and branch assertions retained.
--
--   ∀ gs ∈ (((section14State section14Catalog 1).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 23).take 23, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 170 gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_coverage0005_parentidx0170_specs_0023_0046_timeout_fcc06b3c : ∀ gs ∈ (((section14State section14Catalog 1).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 23).take 23, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 170 gs.1 j := by sorry
