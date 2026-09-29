-- Prove2me | Theorems.Thm_Freiman_section14_s0013_plan0005_specs_0072_0080
-- name    : Freiman.section14_s0013_plan0005_specs_0072_0080
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T11:00:47.212563+00:00
-- url     : https://prove2.me/theorems/c55c3501-9209-4dce-9b41-c9732c365ab5
-- title:
--   Freiman.section14_s0013_plan0005_specs_0072_0080
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 72).take 8, section14SpecValid section14Catalog (section14State section14Catalog 13) ((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_plan0005_specs_0072_0080 : ∀ gs ∈ (((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 72).take 8, section14SpecValid section14Catalog (section14State section14Catalog 13) ((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
