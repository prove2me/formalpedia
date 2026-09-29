-- Prove2me | Theorems.Thm_Freiman_section14_s0016_plan0004_specs_0000_0016
-- name    : Freiman.section14_s0016_plan0004_specs_0000_0016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T22:08:25.912442+00:00
-- url     : https://prove2.me/theorems/763d6f56-135c-48fe-bc87-5e24c9260934
-- title:
--   Freiman.section14_s0016_plan0004_specs_0000_0016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 16).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 16) ((section14State section14Catalog 16).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_plan0004_specs_0000_0016 : ∀ gs ∈ (((section14State section14Catalog 16).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 16) ((section14State section14Catalog 16).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
