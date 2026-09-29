-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plan0007_specs_all
-- name    : Freiman.section14_s0014_plan0007_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:12:41.920537+00:00
-- url     : https://prove2.me/theorems/f06ad29e-a0b9-42e3-bfe8-10ad39dd47d3
-- title:
--   Freiman.section14_s0014_plan0007_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 14).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plan0007_specs_all : ∀ gs ∈ ((section14State section14Catalog 14).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
