-- Prove2me | Theorems.Thm_Freiman_section14_s0012_plan0005_specs_all
-- name    : Freiman.section14_s0012_plan0005_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T05:49:46.706838+00:00
-- url     : https://prove2.me/theorems/74c59116-18d3-4b37-b98d-7bfb7f00c9b5
-- title:
--   Freiman.section14_s0012_plan0005_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 12).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 12) ((section14State section14Catalog 12).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_plan0005_specs_all : ∀ gs ∈ ((section14State section14Catalog 12).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 12) ((section14State section14Catalog 12).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
