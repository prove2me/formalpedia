-- Prove2me | Theorems.Thm_Freiman_section14_s0003_coverage0005_parentidx0010_specs_0016_0024
-- name    : Freiman.section14_s0003_coverage0005_parentidx0010_specs_0016_0024
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T13:05:35.836794+00:00
-- url     : https://prove2.me/theorems/0b7a03d0-9a94-4149-bc0e-8208d9866e3a
-- title:
--   Freiman.section14_s0003_coverage0005_parentidx0010_specs_0016_0024
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 10 gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_coverage0005_parentidx0010_specs_0016_0024 : ∀ gs ∈ (((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 10 gs.1 j := by sorry
