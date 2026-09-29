-- Prove2me | Theorems.Thm_Freiman_section14_s0007_plan0004_specs_0064_0070
-- name    : Freiman.section14_s0007_plan0004_specs_0064_0070
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:55:55.026105+00:00
-- url     : https://prove2.me/theorems/a81d3593-999a-42b3-ab3a-e43077d71d13
-- title:
--   Freiman.section14_s0007_plan0004_specs_0064_0070
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 7).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 6, section14SpecValid section14Catalog (section14State section14Catalog 7) ((section14State section14Catalog 7).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_plan0004_specs_0064_0070 : ∀ gs ∈ (((section14State section14Catalog 7).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 6, section14SpecValid section14Catalog (section14State section14Catalog 7) ((section14State section14Catalog 7).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
