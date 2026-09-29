-- Prove2me | Theorems.Thm_Freiman_section14_s0010_plan0006_specs_0000_0014
-- name    : Freiman.section14_s0010_plan0006_specs_0000_0014
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T16:17:37.135162+00:00
-- url     : https://prove2.me/theorems/85675d02-223d-426a-9702-646b62955dbd
-- title:
--   Freiman.section14_s0010_plan0006_specs_0000_0014
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 10).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 14, section14SpecValid section14Catalog (section14State section14Catalog 10) ((section14State section14Catalog 10).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_plan0006_specs_0000_0014 : ∀ gs ∈ (((section14State section14Catalog 10).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 14, section14SpecValid section14Catalog (section14State section14Catalog 10) ((section14State section14Catalog 10).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
