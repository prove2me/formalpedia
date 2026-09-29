-- Prove2me | Theorems.Thm_Freiman_section14_s0009_plan0005_specs_0080_0091
-- name    : Freiman.section14_s0009_plan0005_specs_0080_0091
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T19:21:36.26911+00:00
-- url     : https://prove2.me/theorems/97c7fdd5-ae55-4f78-af40-cb49820884e6
-- title:
--   Freiman.section14_s0009_plan0005_specs_0080_0091
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 9).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 11, section14SpecValid section14Catalog (section14State section14Catalog 9) ((section14State section14Catalog 9).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_plan0005_specs_0080_0091 : ∀ gs ∈ (((section14State section14Catalog 9).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 11, section14SpecValid section14Catalog (section14State section14Catalog 9) ((section14State section14Catalog 9).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
