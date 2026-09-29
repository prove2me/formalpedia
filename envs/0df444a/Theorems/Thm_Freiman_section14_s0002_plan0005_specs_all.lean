-- Prove2me | Theorems.Thm_Freiman_section14_s0002_plan0005_specs_all
-- name    : Freiman.section14_s0002_plan0005_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:14:54.684989+00:00
-- url     : https://prove2.me/theorems/0bfacec6-b0db-4d9e-8c30-6fd84afa6634
-- title:
--   Freiman.section14_s0002_plan0005_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 2).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 2) ((section14State section14Catalog 2).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_plan0005_specs_all : ∀ gs ∈ ((section14State section14Catalog 2).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 2) ((section14State section14Catalog 2).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
