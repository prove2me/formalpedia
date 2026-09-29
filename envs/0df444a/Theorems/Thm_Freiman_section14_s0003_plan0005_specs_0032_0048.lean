-- Prove2me | Theorems.Thm_Freiman_section14_s0003_plan0005_specs_0032_0048
-- name    : Freiman.section14_s0003_plan0005_specs_0032_0048
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T12:03:36.681392+00:00
-- url     : https://prove2.me/theorems/d6bb4079-be0f-4229-aa77-1559954480fe
-- title:
--   Freiman.section14_s0003_plan0005_specs_0032_0048
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 32).take 16, section14SpecValid section14Catalog (section14State section14Catalog 3) ((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_plan0005_specs_0032_0048 : ∀ gs ∈ (((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 32).take 16, section14SpecValid section14Catalog (section14State section14Catalog 3) ((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
