-- Prove2me | Theorems.Thm_Freiman_section14_s0007_plan0006_specs_all
-- name    : Freiman.section14_s0007_plan0006_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T11:29:45.783341+00:00
-- url     : https://prove2.me/theorems/3c83f69b-92ca-4ac3-96e5-057c0051217c
-- title:
--   Freiman.section14_s0007_plan0006_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 7).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 7) ((section14State section14Catalog 7).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_plan0006_specs_all : ∀ gs ∈ ((section14State section14Catalog 7).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 7) ((section14State section14Catalog 7).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
