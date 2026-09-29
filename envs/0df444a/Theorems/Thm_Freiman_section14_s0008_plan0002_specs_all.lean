-- Prove2me | Theorems.Thm_Freiman_section14_s0008_plan0002_specs_all
-- name    : Freiman.section14_s0008_plan0002_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:12:38.124049+00:00
-- url     : https://prove2.me/theorems/1c55bd4d-4e31-46d6-9f4e-829167305e3f
-- title:
--   Freiman.section14_s0008_plan0002_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 8).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 8) ((section14State section14Catalog 8).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_plan0002_specs_all : ∀ gs ∈ ((section14State section14Catalog 8).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 8) ((section14State section14Catalog 8).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
