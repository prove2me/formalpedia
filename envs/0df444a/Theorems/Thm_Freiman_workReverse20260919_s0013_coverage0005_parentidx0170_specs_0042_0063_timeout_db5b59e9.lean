-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_coverage0005_parentidx0170_specs_0042_0063_timeout_db5b59e9
-- name    : Freiman.workReverse20260919_s0013_coverage0005_parentidx0170_specs_0042_0063_timeout_db5b59e9
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T10:06:21.305118+00:00
-- url     : https://prove2.me/theorems/bb5ce458-d628-4153-8567-0db6f7747085
-- title:
--   Freiman.workReverse20260919_s0013_coverage0005_parentidx0170_specs_0042_0063_timeout_db5b59e9
-- statement:
--   Exact original catalogue proof split into disjoint specification slices and reassembled without changing the target assertion.
--
--   ∀ gs ∈ (((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 42).take 21, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 170 gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_coverage0005_parentidx0170_specs_0042_0063_timeout_db5b59e9 : ∀ gs ∈ (((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 42).take 21, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 170 gs.1 j := by sorry
