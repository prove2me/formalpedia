-- Prove2me | Theorems.Thm_Freiman_section14_s0010_plan0007_specs_all
-- name    : Freiman.section14_s0010_plan0007_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T18:20:11.55279+00:00
-- url     : https://prove2.me/theorems/76d7a28d-6f26-46e5-aeb7-73cae2a548ef
-- title:
--   Freiman.section14_s0010_plan0007_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 10).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 10) ((section14State section14Catalog 10).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_plan0007_specs_all : ∀ gs ∈ ((section14State section14Catalog 10).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 10) ((section14State section14Catalog 10).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
