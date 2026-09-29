-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0005_parentidx0174_specs_0069_0091_native_timeout_682dbc7c
-- name    : Freiman.workReverse20260919_s0005_coverage0005_parentidx0174_specs_0069_0091_native_timeout_682dbc7c
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T04:37:00.521268+00:00
-- url     : https://prove2.me/theorems/7fc6505c-3534-4494-b44b-2fe647cd4a99
-- title:
--   Freiman.workReverse20260919_s0005_coverage0005_parentidx0174_specs_0069_0091_native_timeout_682dbc7c
-- statement:
--   Exact original state5 coverage generator on this strict specification slice; all original goals, state-specific records and branch cases retained.
--
--   ∀ gs ∈ (((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 69).take 22, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 174 gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_coverage0005_parentidx0174_specs_0069_0091_native_timeout_682dbc7c : ∀ gs ∈ (((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 69).take 22, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 174 gs.1 j := by sorry
