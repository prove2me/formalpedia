-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plan0007_specs_0016_0032
-- name    : Freiman.section14_s0014_plan0007_specs_0016_0032
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T01:01:51.130026+00:00
-- url     : https://prove2.me/theorems/ebb7b94a-da0b-419c-a803-43a6c43f7741
-- title:
--   Freiman.section14_s0014_plan0007_specs_0016_0032
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 14).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 16, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plan0007_specs_0016_0032 : ∀ gs ∈ (((section14State section14Catalog 14).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 16, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
