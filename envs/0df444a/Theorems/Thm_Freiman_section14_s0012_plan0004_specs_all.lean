-- Prove2me | Theorems.Thm_Freiman_section14_s0012_plan0004_specs_all
-- name    : Freiman.section14_s0012_plan0004_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T05:48:18.906284+00:00
-- url     : https://prove2.me/theorems/db9e6cd8-f550-4164-ac91-c9cd78cfaf54
-- title:
--   Freiman.section14_s0012_plan0004_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 12).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 12) ((section14State section14Catalog 12).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_plan0004_specs_all : ∀ gs ∈ ((section14State section14Catalog 12).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 12) ((section14State section14Catalog 12).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
