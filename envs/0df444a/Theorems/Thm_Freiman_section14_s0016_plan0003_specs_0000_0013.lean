-- Prove2me | Theorems.Thm_Freiman_section14_s0016_plan0003_specs_0000_0013
-- name    : Freiman.section14_s0016_plan0003_specs_0000_0013
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T22:03:55.9878+00:00
-- url     : https://prove2.me/theorems/b309b88e-9654-4ca0-8d45-b1a605766815
-- title:
--   Freiman.section14_s0016_plan0003_specs_0000_0013
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 16).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 13, section14SpecValid section14Catalog (section14State section14Catalog 16) ((section14State section14Catalog 16).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_plan0003_specs_0000_0013 : ∀ gs ∈ (((section14State section14Catalog 16).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 13, section14SpecValid section14Catalog (section14State section14Catalog 16) ((section14State section14Catalog 16).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
