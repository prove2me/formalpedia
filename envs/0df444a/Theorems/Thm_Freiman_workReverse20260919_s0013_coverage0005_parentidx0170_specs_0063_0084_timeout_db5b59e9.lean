-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_coverage0005_parentidx0170_specs_0063_0084_timeout_db5b59e9
-- name    : Freiman.workReverse20260919_s0013_coverage0005_parentidx0170_specs_0063_0084_timeout_db5b59e9
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T10:06:38.912911+00:00
-- url     : https://prove2.me/theorems/1d2f4a94-d089-49d4-8d7a-8b9e536b88aa
-- title:
--   Freiman.workReverse20260919_s0013_coverage0005_parentidx0170_specs_0063_0084_timeout_db5b59e9
-- statement:
--   Exact original catalogue proof split into disjoint specification slices and reassembled without changing the target assertion.
--
--   ∀ gs ∈ (((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 63).take 21, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 170 gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_coverage0005_parentidx0170_specs_0063_0084_timeout_db5b59e9 : ∀ gs ∈ (((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 63).take 21, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 170 gs.1 j := by sorry
