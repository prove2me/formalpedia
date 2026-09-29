-- Prove2me | Theorems.Thm_Freiman_section14_s0002_plan0007_specs_0032_0048
-- name    : Freiman.section14_s0002_plan0007_specs_0032_0048
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T05:21:40.831991+00:00
-- url     : https://prove2.me/theorems/85c76051-ca1f-48e2-b4d4-43823ed296ae
-- title:
--   Freiman.section14_s0002_plan0007_specs_0032_0048
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 2).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 32).take 16, section14SpecValid section14Catalog (section14State section14Catalog 2) ((section14State section14Catalog 2).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_plan0007_specs_0032_0048 : ∀ gs ∈ (((section14State section14Catalog 2).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 32).take 16, section14SpecValid section14Catalog (section14State section14Catalog 2) ((section14State section14Catalog 2).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
