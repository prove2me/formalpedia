-- Prove2me | Theorems.Thm_Freiman_section14_s0016_plan0007_specs_all
-- name    : Freiman.section14_s0016_plan0007_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T01:02:13.209407+00:00
-- url     : https://prove2.me/theorems/35771c09-90a2-4bd5-a4c5-3b188154ff89
-- title:
--   Freiman.section14_s0016_plan0007_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 16).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 16) ((section14State section14Catalog 16).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_plan0007_specs_all : ∀ gs ∈ ((section14State section14Catalog 16).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 16) ((section14State section14Catalog 16).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
