-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plan0005_specs_0080_0084
-- name    : Freiman.section14_s0014_plan0005_specs_0080_0084
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T00:32:18.40738+00:00
-- url     : https://prove2.me/theorems/7da1a8ab-10d4-43c9-a4fc-8ecb068914fc
-- title:
--   Freiman.section14_s0014_plan0005_specs_0080_0084
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 14).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 4, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plan0005_specs_0080_0084 : ∀ gs ∈ (((section14State section14Catalog 14).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 4, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
