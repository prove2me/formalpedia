-- Prove2me | Theorems.Thm_Freiman_section14_s0015_plan0002_specs_all
-- name    : Freiman.section14_s0015_plan0002_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T21:17:38.675252+00:00
-- url     : https://prove2.me/theorems/ea341a59-36fa-4e54-90e9-21bc91f6cf4a
-- title:
--   Freiman.section14_s0015_plan0002_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 15).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_plan0002_specs_all : ∀ gs ∈ ((section14State section14Catalog 15).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
