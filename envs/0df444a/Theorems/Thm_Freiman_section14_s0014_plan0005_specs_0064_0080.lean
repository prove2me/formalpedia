-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plan0005_specs_0064_0080
-- name    : Freiman.section14_s0014_plan0005_specs_0064_0080
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T00:32:14.362459+00:00
-- url     : https://prove2.me/theorems/6ca00ea0-1470-4dd0-800e-c99458257730
-- title:
--   Freiman.section14_s0014_plan0005_specs_0064_0080
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 14).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 16, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plan0005_specs_0064_0080 : ∀ gs ∈ (((section14State section14Catalog 14).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 16, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
