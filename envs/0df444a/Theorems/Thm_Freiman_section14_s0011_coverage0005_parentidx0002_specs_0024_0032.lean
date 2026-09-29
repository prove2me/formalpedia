-- Prove2me | Theorems.Thm_Freiman_section14_s0011_coverage0005_parentidx0002_specs_0024_0032
-- name    : Freiman.section14_s0011_coverage0005_parentidx0002_specs_0024_0032
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T14:48:42.465651+00:00
-- url     : https://prove2.me/theorems/54f3603c-0c36-4098-9e6b-fbaf1d0279bb
-- title:
--   Freiman.section14_s0011_coverage0005_parentidx0002_specs_0024_0032
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 11).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 24).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 11 2 gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_coverage0005_parentidx0002_specs_0024_0032 : ∀ gs ∈ (((section14State section14Catalog 11).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 24).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 11 2 gs.1 j := by sorry
