-- Prove2me | Theorems.Thm_Freiman_section14_s0007_plan0005_specs_0064_0080
-- name    : Freiman.section14_s0007_plan0005_specs_0064_0080
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T09:00:59.786589+00:00
-- url     : https://prove2.me/theorems/5a833a57-b6b2-464e-8cf1-a818dc18fec1
-- title:
--   Freiman.section14_s0007_plan0005_specs_0064_0080
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 16, section14SpecValid section14Catalog (section14State section14Catalog 7) ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_plan0005_specs_0064_0080 : ∀ gs ∈ (((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 16, section14SpecValid section14Catalog (section14State section14Catalog 7) ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
