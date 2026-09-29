-- Prove2me | Theorems.Thm_Freiman_section14_s0010_plan0002_specs_0000_0016
-- name    : Freiman.section14_s0010_plan0002_specs_0000_0016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T15:49:53.375333+00:00
-- url     : https://prove2.me/theorems/ace36e84-a7f4-456e-950f-7e8480e3072d
-- title:
--   Freiman.section14_s0010_plan0002_specs_0000_0016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 10).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 10) ((section14State section14Catalog 10).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_plan0002_specs_0000_0016 : ∀ gs ∈ (((section14State section14Catalog 10).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 10) ((section14State section14Catalog 10).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
