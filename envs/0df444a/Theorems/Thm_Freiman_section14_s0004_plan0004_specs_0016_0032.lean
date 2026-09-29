-- Prove2me | Theorems.Thm_Freiman_section14_s0004_plan0004_specs_0016_0032
-- name    : Freiman.section14_s0004_plan0004_specs_0016_0032
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T01:37:45.818071+00:00
-- url     : https://prove2.me/theorems/6d9db68b-a3bd-4262-b8a6-2cd9050ce4ee
-- title:
--   Freiman.section14_s0004_plan0004_specs_0016_0032
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 4).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 16, section14SpecValid section14Catalog (section14State section14Catalog 4) ((section14State section14Catalog 4).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_plan0004_specs_0016_0032 : ∀ gs ∈ (((section14State section14Catalog 4).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 16, section14SpecValid section14Catalog (section14State section14Catalog 4) ((section14State section14Catalog 4).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
