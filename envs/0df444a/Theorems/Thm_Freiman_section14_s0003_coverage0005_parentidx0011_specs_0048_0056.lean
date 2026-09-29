-- Prove2me | Theorems.Thm_Freiman_section14_s0003_coverage0005_parentidx0011_specs_0048_0056
-- name    : Freiman.section14_s0003_coverage0005_parentidx0011_specs_0048_0056
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T14:27:12.092649+00:00
-- url     : https://prove2.me/theorems/3a4e4bbf-1c1f-4298-9d23-820fbbb5a811
-- title:
--   Freiman.section14_s0003_coverage0005_parentidx0011_specs_0048_0056
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 48).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 11 gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_coverage0005_parentidx0011_specs_0048_0056 : ∀ gs ∈ (((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 48).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 11 gs.1 j := by sorry
