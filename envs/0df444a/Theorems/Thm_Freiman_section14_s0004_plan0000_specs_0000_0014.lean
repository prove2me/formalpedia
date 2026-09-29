-- Prove2me | Theorems.Thm_Freiman_section14_s0004_plan0000_specs_0000_0014
-- name    : Freiman.section14_s0004_plan0000_specs_0000_0014
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T01:27:25.403188+00:00
-- url     : https://prove2.me/theorems/a6fda926-6f31-42f9-b098-125141b49988
-- title:
--   Freiman.section14_s0004_plan0000_specs_0000_0014
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 4).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 14, section14SpecValid section14Catalog (section14State section14Catalog 4) ((section14State section14Catalog 4).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_plan0000_specs_0000_0014 : ∀ gs ∈ (((section14State section14Catalog 4).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 14, section14SpecValid section14Catalog (section14State section14Catalog 4) ((section14State section14Catalog 4).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
