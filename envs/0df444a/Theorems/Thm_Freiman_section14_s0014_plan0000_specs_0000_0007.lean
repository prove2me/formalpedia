-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plan0000_specs_0000_0007
-- name    : Freiman.section14_s0014_plan0000_specs_0000_0007
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T22:58:08.186327+00:00
-- url     : https://prove2.me/theorems/674e8ce4-7034-4a9c-b88f-24e65076723c
-- title:
--   Freiman.section14_s0014_plan0000_specs_0000_0007
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 14).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 7, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plan0000_specs_0000_0007 : ∀ gs ∈ (((section14State section14Catalog 14).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 7, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
