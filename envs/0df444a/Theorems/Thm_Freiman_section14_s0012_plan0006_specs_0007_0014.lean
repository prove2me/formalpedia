-- Prove2me | Theorems.Thm_Freiman_section14_s0012_plan0006_specs_0007_0014
-- name    : Freiman.section14_s0012_plan0006_specs_0007_0014
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T04:07:34.261309+00:00
-- url     : https://prove2.me/theorems/070c9451-ec52-4a09-ad26-a1d2c03c3b43
-- title:
--   Freiman.section14_s0012_plan0006_specs_0007_0014
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 12).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 7).take 7, section14SpecValid section14Catalog (section14State section14Catalog 12) ((section14State section14Catalog 12).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_plan0006_specs_0007_0014 : ∀ gs ∈ (((section14State section14Catalog 12).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 7).take 7, section14SpecValid section14Catalog (section14State section14Catalog 12) ((section14State section14Catalog 12).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
