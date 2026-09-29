-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plan0001_specs_0000_0013
-- name    : Freiman.section14_s0014_plan0001_specs_0000_0013
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T23:14:55.042058+00:00
-- url     : https://prove2.me/theorems/eed25958-5cfb-432e-b413-a27f5dc5bd49
-- title:
--   Freiman.section14_s0014_plan0001_specs_0000_0013
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 14).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 13, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plan0001_specs_0000_0013 : ∀ gs ∈ (((section14State section14Catalog 14).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 13, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
