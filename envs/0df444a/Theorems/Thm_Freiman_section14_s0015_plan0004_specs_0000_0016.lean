-- Prove2me | Theorems.Thm_Freiman_section14_s0015_plan0004_specs_0000_0016
-- name    : Freiman.section14_s0015_plan0004_specs_0000_0016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T17:21:40.239741+00:00
-- url     : https://prove2.me/theorems/a2094d37-7ce6-4a85-8ddc-380e4709bd69
-- title:
--   Freiman.section14_s0015_plan0004_specs_0000_0016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 15).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_plan0004_specs_0000_0016 : ∀ gs ∈ (((section14State section14Catalog 15).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
