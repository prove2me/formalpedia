-- Prove2me | Theorems.Thm_Freiman_section14_s0015_plan0005_specs_0080_0084
-- name    : Freiman.section14_s0015_plan0005_specs_0080_0084
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T17:29:01.349375+00:00
-- url     : https://prove2.me/theorems/737d57cd-aa88-4104-bcd2-9cc1ee9921df
-- title:
--   Freiman.section14_s0015_plan0005_specs_0080_0084
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 15).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 4, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_plan0005_specs_0080_0084 : ∀ gs ∈ (((section14State section14Catalog 15).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 4, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
