-- Prove2me | Theorems.Thm_Freiman_section14_s0007_plan0002_specs_0000_0016
-- name    : Freiman.section14_s0007_plan0002_specs_0000_0016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:46:20.879989+00:00
-- url     : https://prove2.me/theorems/16739b81-d5b8-4e4a-990c-9b87a77db017
-- title:
--   Freiman.section14_s0007_plan0002_specs_0000_0016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 7).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 7) ((section14State section14Catalog 7).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_plan0002_specs_0000_0016 : ∀ gs ∈ (((section14State section14Catalog 7).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 7) ((section14State section14Catalog 7).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
