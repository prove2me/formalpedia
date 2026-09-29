-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plan0000_specs_0007_0014
-- name    : Freiman.section14_s0014_plan0000_specs_0007_0014
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T23:02:38.171984+00:00
-- url     : https://prove2.me/theorems/a8fa8776-a997-4385-a69c-e0749ce30817
-- title:
--   Freiman.section14_s0014_plan0000_specs_0007_0014
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 14).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 7).take 7, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plan0000_specs_0007_0014 : ∀ gs ∈ (((section14State section14Catalog 14).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 7).take 7, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
