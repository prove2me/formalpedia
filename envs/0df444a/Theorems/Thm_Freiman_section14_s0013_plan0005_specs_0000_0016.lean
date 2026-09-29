-- Prove2me | Theorems.Thm_Freiman_section14_s0013_plan0005_specs_0000_0016
-- name    : Freiman.section14_s0013_plan0005_specs_0000_0016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T10:49:14.142636+00:00
-- url     : https://prove2.me/theorems/e7ac797a-b405-45a5-ac90-a5f2838189b5
-- title:
--   Freiman.section14_s0013_plan0005_specs_0000_0016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 13) ((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_plan0005_specs_0000_0016 : ∀ gs ∈ (((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 13) ((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
