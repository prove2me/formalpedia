-- Prove2me | Theorems.Thm_Freiman_section14_s0010_plan0005_specs_0080_0091
-- name    : Freiman.section14_s0010_plan0005_specs_0080_0091
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T16:13:24.495838+00:00
-- url     : https://prove2.me/theorems/9e51eec8-285c-41f1-9b0a-d4e4e0f555ea
-- title:
--   Freiman.section14_s0010_plan0005_specs_0080_0091
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 10).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 11, section14SpecValid section14Catalog (section14State section14Catalog 10) ((section14State section14Catalog 10).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_plan0005_specs_0080_0091 : ∀ gs ∈ (((section14State section14Catalog 10).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 11, section14SpecValid section14Catalog (section14State section14Catalog 10) ((section14State section14Catalog 10).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
