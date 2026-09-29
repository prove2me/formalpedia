-- Prove2me | Theorems.Thm_Freiman_section14_s0013_plan0001_specs_0000_0013
-- name    : Freiman.section14_s0013_plan0001_specs_0000_0013
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T09:51:22.687927+00:00
-- url     : https://prove2.me/theorems/b193fd5b-87d8-4cc5-9a15-c021a168f0ca
-- title:
--   Freiman.section14_s0013_plan0001_specs_0000_0013
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 13).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 13, section14SpecValid section14Catalog (section14State section14Catalog 13) ((section14State section14Catalog 13).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_plan0001_specs_0000_0013 : ∀ gs ∈ (((section14State section14Catalog 13).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 13, section14SpecValid section14Catalog (section14State section14Catalog 13) ((section14State section14Catalog 13).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
