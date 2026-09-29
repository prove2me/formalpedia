-- Prove2me | Theorems.Thm_Freiman_section14_s0015_plan0000_specs_0000_0014
-- name    : Freiman.section14_s0015_plan0000_specs_0000_0014
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T17:12:43.065179+00:00
-- url     : https://prove2.me/theorems/9a3b28df-e0f5-41e1-8b0a-75adf6473fa2
-- title:
--   Freiman.section14_s0015_plan0000_specs_0000_0014
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 15).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 14, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_plan0000_specs_0000_0014 : ∀ gs ∈ (((section14State section14Catalog 15).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 14, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
