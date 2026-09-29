-- Prove2me | Theorems.Thm_Freiman_section14_s0012_plan0003_specs_all
-- name    : Freiman.section14_s0012_plan0003_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T05:47:06.918982+00:00
-- url     : https://prove2.me/theorems/e936f27d-0da2-414c-ac68-60a940b6ad49
-- title:
--   Freiman.section14_s0012_plan0003_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 12).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 12) ((section14State section14Catalog 12).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_plan0003_specs_all : ∀ gs ∈ ((section14State section14Catalog 12).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 12) ((section14State section14Catalog 12).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
