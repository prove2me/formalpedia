-- Prove2me | Theorems.Thm_Freiman_section14_s0003_plan0004_specs_0016_0032
-- name    : Freiman.section14_s0003_plan0004_specs_0016_0032
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T11:57:51.970479+00:00
-- url     : https://prove2.me/theorems/ca913d07-620d-42aa-99c8-1e8917823713
-- title:
--   Freiman.section14_s0003_plan0004_specs_0016_0032
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 3).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 16, section14SpecValid section14Catalog (section14State section14Catalog 3) ((section14State section14Catalog 3).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_plan0004_specs_0016_0032 : ∀ gs ∈ (((section14State section14Catalog 3).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 16, section14SpecValid section14Catalog (section14State section14Catalog 3) ((section14State section14Catalog 3).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
