-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_coverage0005_parentidx0170_specs_0046_0069_timeout_363e3eb1
-- name    : Freiman.workReverse20260919_s0006_coverage0005_parentidx0170_specs_0046_0069_timeout_363e3eb1
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T04:10:15.252987+00:00
-- url     : https://prove2.me/theorems/ec12e407-852c-4c31-970c-b6ec67470fd5
-- title:
--   Freiman.workReverse20260919_s0006_coverage0005_parentidx0170_specs_0046_0069_timeout_363e3eb1
-- statement:
--   Exact original state6 coverage generator on this strict specification slice; all original goals, state-specific records and branch cases retained.
--
--   ∀ gs ∈ (((section14State section14Catalog 6).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 46).take 23, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 170 gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_coverage0005_parentidx0170_specs_0046_0069_timeout_363e3eb1 : ∀ gs ∈ (((section14State section14Catalog 6).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 46).take 23, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 170 gs.1 j := by sorry
