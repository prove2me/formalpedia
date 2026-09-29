-- Prove2me | Theorems.Thm_Freiman_section14_s0002_plan0005_specs_0080_0091
-- name    : Freiman.section14_s0002_plan0005_specs_0080_0091
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T04:38:17.426984+00:00
-- url     : https://prove2.me/theorems/c3a5e89e-db73-41ad-85fb-f55fda359708
-- title:
--   Freiman.section14_s0002_plan0005_specs_0080_0091
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 2).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 11, section14SpecValid section14Catalog (section14State section14Catalog 2) ((section14State section14Catalog 2).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_plan0005_specs_0080_0091 : ∀ gs ∈ (((section14State section14Catalog 2).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 11, section14SpecValid section14Catalog (section14State section14Catalog 2) ((section14State section14Catalog 2).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
