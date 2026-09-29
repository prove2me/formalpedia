-- Prove2me | Theorems.Thm_Freiman_section14_s0008_plan0003_specs_0016_0021
-- name    : Freiman.section14_s0008_plan0003_specs_0016_0021
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T06:17:50.231983+00:00
-- url     : https://prove2.me/theorems/49b117ca-f868-442a-8435-4bbbc010b1e5
-- title:
--   Freiman.section14_s0008_plan0003_specs_0016_0021
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 8).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 5, section14SpecValid section14Catalog (section14State section14Catalog 8) ((section14State section14Catalog 8).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_plan0003_specs_0016_0021 : ∀ gs ∈ (((section14State section14Catalog 8).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 5, section14SpecValid section14Catalog (section14State section14Catalog 8) ((section14State section14Catalog 8).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
