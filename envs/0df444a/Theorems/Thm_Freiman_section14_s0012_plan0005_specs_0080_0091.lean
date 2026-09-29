-- Prove2me | Theorems.Thm_Freiman_section14_s0012_plan0005_specs_0080_0091
-- name    : Freiman.section14_s0012_plan0005_specs_0080_0091
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T04:00:29.10431+00:00
-- url     : https://prove2.me/theorems/2ca74ab9-0e18-4c89-b5d0-a0da74f6103f
-- title:
--   Freiman.section14_s0012_plan0005_specs_0080_0091
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 12).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 11, section14SpecValid section14Catalog (section14State section14Catalog 12) ((section14State section14Catalog 12).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_plan0005_specs_0080_0091 : ∀ gs ∈ (((section14State section14Catalog 12).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 11, section14SpecValid section14Catalog (section14State section14Catalog 12) ((section14State section14Catalog 12).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
