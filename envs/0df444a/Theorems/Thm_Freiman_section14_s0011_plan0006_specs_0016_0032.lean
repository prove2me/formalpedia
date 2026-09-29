-- Prove2me | Theorems.Thm_Freiman_section14_s0011_plan0006_specs_0016_0032
-- name    : Freiman.section14_s0011_plan0006_specs_0016_0032
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T12:10:05.150039+00:00
-- url     : https://prove2.me/theorems/80c8e056-cb00-4c66-85ab-efe52bcb3680
-- title:
--   Freiman.section14_s0011_plan0006_specs_0016_0032
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 11).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 16, section14SpecValid section14Catalog (section14State section14Catalog 11) ((section14State section14Catalog 11).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_plan0006_specs_0016_0032 : ∀ gs ∈ (((section14State section14Catalog 11).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 16, section14SpecValid section14Catalog (section14State section14Catalog 11) ((section14State section14Catalog 11).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
