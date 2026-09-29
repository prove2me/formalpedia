-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0005_parentidx0170_specs_0023_0046_timeout_f65d7d56
-- name    : Freiman.workReverse20260919_s0005_coverage0005_parentidx0170_specs_0023_0046_timeout_f65d7d56
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T04:03:35.971984+00:00
-- url     : https://prove2.me/theorems/e0630f44-28b5-4f4e-9fe9-f2e95611c288
-- title:
--   Freiman.workReverse20260919_s0005_coverage0005_parentidx0170_specs_0023_0046_timeout_f65d7d56
-- statement:
--   Exact original state5 coverage generator on this strict specification slice; all original goals, state-specific records and branch cases retained.
--
--   ∀ gs ∈ (((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 23).take 23, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 170 gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_coverage0005_parentidx0170_specs_0023_0046_timeout_f65d7d56 : ∀ gs ∈ (((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 23).take 23, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 170 gs.1 j := by sorry
