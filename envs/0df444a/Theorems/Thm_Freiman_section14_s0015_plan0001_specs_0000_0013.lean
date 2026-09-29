-- Prove2me | Theorems.Thm_Freiman_section14_s0015_plan0001_specs_0000_0013
-- name    : Freiman.section14_s0015_plan0001_specs_0000_0013
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T17:13:28.271894+00:00
-- url     : https://prove2.me/theorems/2884a058-52e1-49c8-b8a6-89ac3a99e39b
-- title:
--   Freiman.section14_s0015_plan0001_specs_0000_0013
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 15).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 13, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_plan0001_specs_0000_0013 : ∀ gs ∈ (((section14State section14Catalog 15).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 13, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
