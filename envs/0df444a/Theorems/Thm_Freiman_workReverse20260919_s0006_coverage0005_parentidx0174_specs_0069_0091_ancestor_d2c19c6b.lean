-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_coverage0005_parentidx0174_specs_0069_0091_ancestor_d2c19c6b
-- name    : Freiman.workReverse20260919_s0006_coverage0005_parentidx0174_specs_0069_0091_ancestor_d2c19c6b
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T04:39:04.620098+00:00
-- url     : https://prove2.me/theorems/23470582-010c-4c17-95c1-fe58a4191621
-- title:
--   Freiman.workReverse20260919_s0006_coverage0005_parentidx0174_specs_0069_0091_ancestor_d2c19c6b
-- statement:
--   Exact original state6 coverage generator on this strict specification slice; all original goals, state-specific records and branch cases retained.
--
--   ∀ gs ∈ (((section14State section14Catalog 6).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 69).take 22, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 174 gs.1 j
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_coverage0005_parentidx0174_specs_0069_0091_ancestor_d2c19c6b : ∀ gs ∈ (((section14State section14Catalog 6).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 69).take 22, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 174 gs.1 j := by sorry
