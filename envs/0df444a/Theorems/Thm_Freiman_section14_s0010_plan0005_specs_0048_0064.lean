-- Prove2me | Theorems.Thm_Freiman_section14_s0010_plan0005_specs_0048_0064
-- name    : Freiman.section14_s0010_plan0005_specs_0048_0064
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T16:10:16.051684+00:00
-- url     : https://prove2.me/theorems/f30008a0-48ef-4804-af87-6ce74f6e652a
-- title:
--   Freiman.section14_s0010_plan0005_specs_0048_0064
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 10).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 48).take 16, section14SpecValid section14Catalog (section14State section14Catalog 10) ((section14State section14Catalog 10).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_plan0005_specs_0048_0064 : ∀ gs ∈ (((section14State section14Catalog 10).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 48).take 16, section14SpecValid section14Catalog (section14State section14Catalog 10) ((section14State section14Catalog 10).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
