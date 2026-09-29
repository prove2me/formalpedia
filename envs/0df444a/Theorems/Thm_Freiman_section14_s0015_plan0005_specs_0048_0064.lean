-- Prove2me | Theorems.Thm_Freiman_section14_s0015_plan0005_specs_0048_0064
-- name    : Freiman.section14_s0015_plan0005_specs_0048_0064
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T17:28:47.126989+00:00
-- url     : https://prove2.me/theorems/fa807efd-4821-412e-8559-20657a81c0a2
-- title:
--   Freiman.section14_s0015_plan0005_specs_0048_0064
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 15).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 48).take 16, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_plan0005_specs_0048_0064 : ∀ gs ∈ (((section14State section14Catalog 15).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 48).take 16, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
