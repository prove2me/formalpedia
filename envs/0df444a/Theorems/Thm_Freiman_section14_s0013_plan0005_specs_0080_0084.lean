-- Prove2me | Theorems.Thm_Freiman_section14_s0013_plan0005_specs_0080_0084
-- name    : Freiman.section14_s0013_plan0005_specs_0080_0084
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T10:54:10.816414+00:00
-- url     : https://prove2.me/theorems/098ccb41-0fc2-4443-9e4b-deb3e9a7968b
-- title:
--   Freiman.section14_s0013_plan0005_specs_0080_0084
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 4, section14SpecValid section14Catalog (section14State section14Catalog 13) ((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_plan0005_specs_0080_0084 : ∀ gs ∈ (((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 4, section14SpecValid section14Catalog (section14State section14Catalog 13) ((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
