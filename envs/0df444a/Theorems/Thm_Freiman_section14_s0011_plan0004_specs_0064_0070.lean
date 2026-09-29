-- Prove2me | Theorems.Thm_Freiman_section14_s0011_plan0004_specs_0064_0070
-- name    : Freiman.section14_s0011_plan0004_specs_0064_0070
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T11:57:38.578987+00:00
-- url     : https://prove2.me/theorems/1df78f36-6bcd-407a-819d-20747a365795
-- title:
--   Freiman.section14_s0011_plan0004_specs_0064_0070
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 11).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 6, section14SpecValid section14Catalog (section14State section14Catalog 11) ((section14State section14Catalog 11).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_plan0004_specs_0064_0070 : ∀ gs ∈ (((section14State section14Catalog 11).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 6, section14SpecValid section14Catalog (section14State section14Catalog 11) ((section14State section14Catalog 11).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
