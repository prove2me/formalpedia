-- Prove2me | Theorems.Thm_Freiman_section14_s0015_plan0004_specs_0048_0063
-- name    : Freiman.section14_s0015_plan0004_specs_0048_0063
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T17:23:58.236035+00:00
-- url     : https://prove2.me/theorems/93f59010-5ae6-4462-95e4-97be05746b2d
-- title:
--   Freiman.section14_s0015_plan0004_specs_0048_0063
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 15).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 48).take 15, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_plan0004_specs_0048_0063 : ∀ gs ∈ (((section14State section14Catalog 15).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 48).take 15, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
