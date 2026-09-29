-- Prove2me | Theorems.Thm_Freiman_section14_s0013_plan0004_specs_0000_0016
-- name    : Freiman.section14_s0013_plan0004_specs_0000_0016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T10:35:24.17019+00:00
-- url     : https://prove2.me/theorems/5aa9c776-deda-487d-8ab0-4518109bef72
-- title:
--   Freiman.section14_s0013_plan0004_specs_0000_0016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 13).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 13) ((section14State section14Catalog 13).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_plan0004_specs_0000_0016 : ∀ gs ∈ (((section14State section14Catalog 13).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 13) ((section14State section14Catalog 13).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
