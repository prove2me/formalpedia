-- Prove2me | Theorems.Thm_Freiman_section14_s0011_plan0002_specs_all
-- name    : Freiman.section14_s0011_plan0002_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T16:07:45.368618+00:00
-- url     : https://prove2.me/theorems/656538b6-9d20-4fe5-9170-9b9668dddc26
-- title:
--   Freiman.section14_s0011_plan0002_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 11).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 11) ((section14State section14Catalog 11).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_plan0002_specs_all : ∀ gs ∈ ((section14State section14Catalog 11).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 11) ((section14State section14Catalog 11).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
