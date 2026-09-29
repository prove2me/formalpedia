-- Prove2me | Theorems.Thm_Freiman_section14_s0013_plan0005_specs_0064_0072
-- name    : Freiman.section14_s0013_plan0005_specs_0064_0072
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T10:56:03.507324+00:00
-- url     : https://prove2.me/theorems/84afbdac-9bf9-40b7-a332-2591a2dfdec4
-- title:
--   Freiman.section14_s0013_plan0005_specs_0064_0072
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 8, section14SpecValid section14Catalog (section14State section14Catalog 13) ((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_plan0005_specs_0064_0072 : ∀ gs ∈ (((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 8, section14SpecValid section14Catalog (section14State section14Catalog 13) ((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
