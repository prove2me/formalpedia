-- Prove2me | Theorems.Thm_Freiman_section14_s0015_coverage0005_parentidx0010_specs_all
-- name    : Freiman.section14_s0015_coverage0005_parentidx0010_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T20:43:56.629488+00:00
-- url     : https://prove2.me/theorems/ce6a995b-4448-4dbd-a47b-295bca7f4fff
-- title:
--   Freiman.section14_s0015_coverage0005_parentidx0010_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 15).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 15 10 gs.1 j
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_coverage0005_parentidx0010_specs_all : ∀ gs ∈ ((section14State section14Catalog 15).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 15 10 gs.1 j := by sorry
