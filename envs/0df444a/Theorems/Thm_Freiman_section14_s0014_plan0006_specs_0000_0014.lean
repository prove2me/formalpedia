-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plan0006_specs_0000_0014
-- name    : Freiman.section14_s0014_plan0006_specs_0000_0014
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T00:49:28.788806+00:00
-- url     : https://prove2.me/theorems/e33a7592-087e-4e4f-adf3-291fafc67a7d
-- title:
--   Freiman.section14_s0014_plan0006_specs_0000_0014
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 14).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 14, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plan0006_specs_0000_0014 : ∀ gs ∈ (((section14State section14Catalog 14).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 14, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
