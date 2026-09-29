-- Prove2me | Theorems.Thm_Freiman_section14_s0003_coverage0005_parentidx0010_specs_0040_0048
-- name    : Freiman.section14_s0003_coverage0005_parentidx0010_specs_0040_0048
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T13:18:29.980692+00:00
-- url     : https://prove2.me/theorems/e8021d32-f680-4ca2-95ee-2e17626fdadc
-- title:
--   Freiman.section14_s0003_coverage0005_parentidx0010_specs_0040_0048
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 40).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 10 gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_coverage0005_parentidx0010_specs_0040_0048 : ∀ gs ∈ (((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 40).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 10 gs.1 j := by sorry
