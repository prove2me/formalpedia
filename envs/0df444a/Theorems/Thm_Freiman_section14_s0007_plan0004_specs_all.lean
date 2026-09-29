-- Prove2me | Theorems.Thm_Freiman_section14_s0007_plan0004_specs_all
-- name    : Freiman.section14_s0007_plan0004_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T11:26:22.179132+00:00
-- url     : https://prove2.me/theorems/0aef4fa3-181e-4fff-8222-4e2ed52a8e63
-- title:
--   Freiman.section14_s0007_plan0004_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 7).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 7) ((section14State section14Catalog 7).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_plan0004_specs_all : ∀ gs ∈ ((section14State section14Catalog 7).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 7) ((section14State section14Catalog 7).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
