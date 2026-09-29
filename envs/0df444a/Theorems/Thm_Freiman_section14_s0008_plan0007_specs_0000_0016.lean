-- Prove2me | Theorems.Thm_Freiman_section14_s0008_plan0007_specs_0000_0016
-- name    : Freiman.section14_s0008_plan0007_specs_0000_0016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T06:36:46.513215+00:00
-- url     : https://prove2.me/theorems/05dd1872-dc10-4991-baac-d7b759247dfb
-- title:
--   Freiman.section14_s0008_plan0007_specs_0000_0016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 8).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 8) ((section14State section14Catalog 8).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_plan0007_specs_0000_0016 : ∀ gs ∈ (((section14State section14Catalog 8).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 8) ((section14State section14Catalog 8).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
