-- Prove2me | Theorems.Thm_Freiman_section14_s0015_coverage0005_parentidx0010_specs_0032_0040
-- name    : Freiman.section14_s0015_coverage0005_parentidx0010_specs_0032_0040
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T20:05:53.502903+00:00
-- url     : https://prove2.me/theorems/8783278b-3957-4d5f-bf01-807c0e2172fc
-- title:
--   Freiman.section14_s0015_coverage0005_parentidx0010_specs_0032_0040
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 15).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 32).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 15 10 gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_coverage0005_parentidx0010_specs_0032_0040 : ∀ gs ∈ (((section14State section14Catalog 15).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 32).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 15 10 gs.1 j := by sorry
