-- Prove2me | Theorems.Thm_Freiman_section14_s0015_coverage0005_parentidx0010_specs_0000_0008
-- name    : Freiman.section14_s0015_coverage0005_parentidx0010_specs_0000_0008
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T19:17:48.351847+00:00
-- url     : https://prove2.me/theorems/9255adf2-6e78-4399-9a0c-73da026b563a
-- title:
--   Freiman.section14_s0015_coverage0005_parentidx0010_specs_0000_0008
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 15).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 15 10 gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_coverage0005_parentidx0010_specs_0000_0008 : ∀ gs ∈ (((section14State section14Catalog 15).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 15 10 gs.1 j := by sorry
