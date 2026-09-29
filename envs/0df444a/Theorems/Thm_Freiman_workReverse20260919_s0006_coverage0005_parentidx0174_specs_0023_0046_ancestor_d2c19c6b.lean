-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_coverage0005_parentidx0174_specs_0023_0046_ancestor_d2c19c6b
-- name    : Freiman.workReverse20260919_s0006_coverage0005_parentidx0174_specs_0023_0046_ancestor_d2c19c6b
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T04:28:34.755012+00:00
-- url     : https://prove2.me/theorems/a39104c9-cc5e-4de6-bfb9-b1573c7097be
-- title:
--   Freiman.workReverse20260919_s0006_coverage0005_parentidx0174_specs_0023_0046_ancestor_d2c19c6b
-- statement:
--   Exact original state6 coverage generator on this strict specification slice; all original goals, state-specific records and branch cases retained.
--
--   ∀ gs ∈ (((section14State section14Catalog 6).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 23).take 23, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 174 gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_coverage0005_parentidx0174_specs_0023_0046_ancestor_d2c19c6b : ∀ gs ∈ (((section14State section14Catalog 6).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 23).take 23, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 174 gs.1 j := by sorry
