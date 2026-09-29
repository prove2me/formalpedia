-- Prove2me | Theorems.Thm_Freiman_section14_s0003_plan0004_specs_0064_0070
-- name    : Freiman.section14_s0003_plan0004_specs_0064_0070
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T11:58:44.108363+00:00
-- url     : https://prove2.me/theorems/2c1a309f-7992-43cb-9c9f-9b55a74fe229
-- title:
--   Freiman.section14_s0003_plan0004_specs_0064_0070
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 3).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 6, section14SpecValid section14Catalog (section14State section14Catalog 3) ((section14State section14Catalog 3).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_plan0004_specs_0064_0070 : ∀ gs ∈ (((section14State section14Catalog 3).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 6, section14SpecValid section14Catalog (section14State section14Catalog 3) ((section14State section14Catalog 3).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
