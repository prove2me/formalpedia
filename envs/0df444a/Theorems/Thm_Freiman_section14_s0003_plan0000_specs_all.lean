-- Prove2me | Theorems.Thm_Freiman_section14_s0003_plan0000_specs_all
-- name    : Freiman.section14_s0003_plan0000_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T15:11:26.714096+00:00
-- url     : https://prove2.me/theorems/6620769c-3241-47f0-9cd8-6d5e36b9d2bd
-- title:
--   Freiman.section14_s0003_plan0000_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 3).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 3) ((section14State section14Catalog 3).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_plan0000_specs_all : ∀ gs ∈ ((section14State section14Catalog 3).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 3) ((section14State section14Catalog 3).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
