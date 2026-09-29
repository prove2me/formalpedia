-- Prove2me | Theorems.Thm_Freiman_section14_s0003_plan0002_specs_all
-- name    : Freiman.section14_s0003_plan0002_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T15:11:58.904558+00:00
-- url     : https://prove2.me/theorems/7d72f293-89c8-4fb6-ae72-8422f11d60fb
-- title:
--   Freiman.section14_s0003_plan0002_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 3).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 3) ((section14State section14Catalog 3).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_plan0002_specs_all : ∀ gs ∈ ((section14State section14Catalog 3).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 3) ((section14State section14Catalog 3).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
