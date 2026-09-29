-- Prove2me | Theorems.Thm_Freiman_section14_s0007_plan0001_specs_all
-- name    : Freiman.section14_s0007_plan0001_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T11:23:01.692816+00:00
-- url     : https://prove2.me/theorems/f4b0d19b-f4c5-49e6-8a59-0a9d8731ea2c
-- title:
--   Freiman.section14_s0007_plan0001_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 7).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 7) ((section14State section14Catalog 7).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_plan0001_specs_all : ∀ gs ∈ ((section14State section14Catalog 7).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 7) ((section14State section14Catalog 7).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
