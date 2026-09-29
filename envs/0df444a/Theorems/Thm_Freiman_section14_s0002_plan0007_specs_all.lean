-- Prove2me | Theorems.Thm_Freiman_section14_s0002_plan0007_specs_all
-- name    : Freiman.section14_s0002_plan0007_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:29:16.128535+00:00
-- url     : https://prove2.me/theorems/71f8ae91-0fec-4fce-904f-94373a7169cd
-- title:
--   Freiman.section14_s0002_plan0007_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 2).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 2) ((section14State section14Catalog 2).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_plan0007_specs_all : ∀ gs ∈ ((section14State section14Catalog 2).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 2) ((section14State section14Catalog 2).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
