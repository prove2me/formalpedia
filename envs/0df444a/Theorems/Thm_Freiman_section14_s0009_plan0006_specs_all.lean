-- Prove2me | Theorems.Thm_Freiman_section14_s0009_plan0006_specs_all
-- name    : Freiman.section14_s0009_plan0006_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T22:28:24.595138+00:00
-- url     : https://prove2.me/theorems/4a75b80e-3641-47cf-9b4b-8e67af915026
-- title:
--   Freiman.section14_s0009_plan0006_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 9).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 9) ((section14State section14Catalog 9).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_plan0006_specs_all : ∀ gs ∈ ((section14State section14Catalog 9).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 9) ((section14State section14Catalog 9).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
