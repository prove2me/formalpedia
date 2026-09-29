-- Prove2me | Theorems.Thm_Freiman_section14_s0002_plan0004_specs_0064_0070
-- name    : Freiman.section14_s0002_plan0004_specs_0064_0070
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T04:23:08.803387+00:00
-- url     : https://prove2.me/theorems/43aa8351-83ca-489d-9b0d-7b21564def38
-- title:
--   Freiman.section14_s0002_plan0004_specs_0064_0070
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 2).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 6, section14SpecValid section14Catalog (section14State section14Catalog 2) ((section14State section14Catalog 2).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_plan0004_specs_0064_0070 : ∀ gs ∈ (((section14State section14Catalog 2).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 6, section14SpecValid section14Catalog (section14State section14Catalog 2) ((section14State section14Catalog 2).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
